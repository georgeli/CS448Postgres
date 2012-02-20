/*-------------------------------------------------------------------------
 *
 * nodeHashjoin.c
 *	  Routines to handle hash join nodes
 *
 * Portions Copyright (c) 1996-2005, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  $PostgreSQL: pgsql/src/backend/executor/nodeHashjoin.c,v 1.75.2.3 2005/11/28 23:46:24 tgl Exp $
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "executor/executor.h"
#include "executor/hashjoin.h"
#include "executor/nodeHash.h"
#include "executor/nodeHashjoin.h"
#include "optimizer/clauses.h"
#include "utils/memutils.h"


static TupleTableSlot *ExecHashJoinOuterGetTuple(HashState *outerNode,
						  HashJoinState *hjstate,
						  uint32 *hashvalue);
static TupleTableSlot *ExecHashJoinGetSavedTuple(HashJoinState *hjstate,
						  BufFile *file,
						  uint32 *hashvalue,
						  TupleTableSlot *tupleSlot);
static int	ExecHashJoinNewBatch(HashJoinState *hjstate);


/* ----------------------------------------------------------------
 *		ExecHashJoin
 *
 *		This function implements the Hybrid Hashjoin algorithm.
 *
 *		Note: the relation we build hash table on is the "inner"
 *			  the other one is "outer".
 * ----------------------------------------------------------------
 * 		CS448
 * 		
 * 		This function implements the Symmetric Hash Join algorithm.
 * ----------------------------------------------------------------
 */
TupleTableSlot *				/* return: a tuple or NULL */
ExecHashJoin(HashJoinState *node)
{
	HashState  *outerNode;
	HashState  *innerNode;
	List	   *joinqual;
	List	   *otherqual;
	TupleTableSlot *buildtuple;
	ExprContext *econtext;
	ExprDoneCond isDone;
	HashJoinTable innertable;
	HashJoinTable outertable;
	HeapTuple	curtuple;
	TupleTableSlot *probeTupleSlot;
	uint32		hashvalue;
	int			batchno;

	elog(INFO, "Starting hash join");
	/*
	 * get information from HashJoin node
	 */
	elog(INFO, "Getting information from HashJoin node.");
	joinqual = node->js.joinqual;
	otherqual = node->js.ps.qual;
	innerNode = (HashState *) innerPlanState(node);
	outerNode = (HashState *) outerPlanState(node);

	/*
	 * get information from HashJoin state
	 */
	elog(INFO, "Getting information from HashJoin state.");
	innertable = node->hj_InnerTable;
	outertable = node->hj_OuterTable;
	econtext = node->js.ps.ps_ExprContext;

	/*
	 * Check to see if we're still projecting out tuples from a previous join
	 * tuple (because there is a function-returning-set in the projection
	 * expressions).  If so, try to project another one.
	 */
	elog(INFO, "Check for Projection.");
	if (node->js.ps.ps_TupFromTlist)
	{
		TupleTableSlot *result;
		elog(INFO, "Projecting.");

		result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);
		if (isDone == ExprMultipleResult)
			return result;
		/* Done with that source tuple... */
		node->js.ps.ps_TupFromTlist = false;
	}

	/*
	 * If we're doing an IN join, we want to return at most one row per outer
	 * tuple; so we can stop scanning the inner scan if we matched on the
	 * previous try.
	 */
	elog(INFO, "Checking for IN Join");
	if (node->js.jointype == JOIN_IN && node->hj_MatchedTuple)
		node->hj_NeedNew = true;

	/*
	 * Reset per-tuple memory context to free any expression evaluation
	 * storage allocated in the previous tuple cycle.  Note this can't happen
	 * until we're done projecting out tuples from a join tuple.
	 */
	ResetExprContext(econtext);

	/*
	 * if this is the first call, build the hash table for both relations
	 */
	if (innertable == NULL)
	{
		elog(INFO, "Building hash tables");
		/*
		 * create the hash table
		 */
		innertable = ExecHashTableCreate((Hash *) innerNode->ps.plan,
										node->hj_HashOperators);
		node->hj_InnerTable = innertable;
		innerNode->hashtable = innertable;
		
		outertable = ExecHashTableCreate((Hash *) outerNode->ps.plan, 
										node->hj_HashOperators);
		node->hj_OuterTable = outertable;
		outerNode->hashtable = outertable;
		
		/*
		 * need to remember whether nbatch has increased since we began
		 * scanning the outer relation
		 */
		innertable->nbatch_outstart = innertable->nbatch;

		/*
		 * Reset OuterNotEmpty for scan.  (It's OK if we fetched a tuple
		 * above, because ExecHashJoinOuterGetTuple will immediately
		 * set it again.)
		 */
		node->hj_OuterNotEmpty = false;
	}

	/*
	 * run the symmetric hash join process.
	 */
	for (;;)
	{
		if (node->hj_NeedNew)
		{
			elog(INFO, "Fetching new probe tuple.");
			/*
			 * If we don't have a tuple, decide on which relation we need to get, and get it.
			 * We will always start with outer (hj_FromInner == false)
			 */
			if (node->hj_FromInner) 
			{
				elog(INFO, "Fetching from inner relation.");
				/*
				 * Fetch a tuple from the inner relation, building its hash table in the process
				 * Since ExecProcNode is invoked in ExecHashJoinOuterGetTuple, it does not need to be invoked again.
				 */
				probeTupleSlot = ExecHashJoinOuterGetTuple(innerNode, node, &hashvalue);
				
				if (TupIsNull(probeTupleSlot)) 
				{
					node->hj_InnerNotEmpty = false;
					/*
					 * If both relations are empty, we're done.
					 */
					if (!node->hj_InnerNotEmpty && !node->hj_OuterNotEmpty) return NULL;
				}
				node->js.ps.ps_OuterTupleSlot = probeTupleSlot;
				econtext->ecxt_outertuple = probeTupleSlot;
				node->hj_NeedNew = false;
				node->hj_MatchedTuple = false;
				
				/*
				 * Probe the outer table with the probe tuple
				 * Get the hash value of the probe tuple first
				 */
				node->hj_CurHashValue = hashvalue;
				ExecHashGetBucketAndBatch(outertable, hashvalue,
										  &node->hj_CurBucketNo, &batchno);
				node->hj_CurTuple = NULL;
			} else {
				/*
				 * Fetch a tuple from the outer relation, building its hash table in the process
				 */
				elog(INFO, "Fetching from outer relation.");
				probeTupleSlot = ExecHashJoinOuterGetTuple(outerNode, node, &hashvalue);
	
				if (TupIsNull(probeTupleSlot))
				{
					node->hj_OuterNotEmpty = false;
					/*
					 * If both relations are empty, we're done.
					 */
					if (!node->hj_InnerNotEmpty && !node->hj_OuterNotEmpty) return NULL;
				}
				node->js.ps.ps_OuterTupleSlot = probeTupleSlot;
				econtext->ecxt_outertuple = probeTupleSlot;
				node->hj_NeedNew = false;
				node->hj_MatchedTuple = false;
				/*
				 * Probe the inner table with the probe tuple
				 * Get the hash value of the probe tuple first
				 */
				node->hj_CurHashValue = hashvalue;
				ExecHashGetBucketAndBatch(innertable, hashvalue,
										  &node->hj_CurBucketNo, &batchno);
				node->hj_CurTuple = NULL;
			}
		}
		/*
		 * OK, scan the selected hash bucket for matches
		 */
		elog(INFO, "Probing build relation.");
		for (;;)
		{
			curtuple = ExecScanHashBucket(node, econtext);
			if (curtuple == NULL)
			{
				elog(INFO, "Probe returned no matches in the current bucket.");
				/*
				 * No match in the current hash bucket.
				 * But maybe the build relation's hash table isn't completely built yet.
				 * We need to flip the build/probe relations and keep building the hash table.
				 */
				node->hj_NeedNew = true;
				node->hj_FromInner = !node->hj_FromInner;
				break;		/* out of loop over hash bucket */
			}

			/*
			 * we've got a match, but still need to test non-hashed quals
			 */
			elog(INFO, "Probe returned a match.");
			buildtuple = ExecStoreTuple(curtuple,
									  node->hj_FromInner ? node->hj_OuterTupleSlot : node->hj_InnerTupleSlot,
									  InvalidBuffer,
									  false);	/* don't pfree this tuple */
			econtext->ecxt_innertuple = buildtuple;

			/* reset temp memory each time to avoid leaks from qual expr */
			ResetExprContext(econtext);

			/*
			 * if we pass the qual, then save state for next call and have
			 * ExecProject form the projection, store it in the tuple table,
			 * and return the slot.
			 *
			 * Only the joinquals determine MatchedOuter status, but all quals
			 * must pass to actually return the tuple.
			 */
			if (joinqual == NIL || ExecQual(joinqual, econtext, false))
			{
				elog(INFO, "Actual value matched, too");
				node->hj_MatchedTuple = true;

				if (otherqual == NIL || ExecQual(otherqual, econtext, false))
				{
					TupleTableSlot *result;

					result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);

					if (isDone != ExprEndResult)
					{
						elog(INFO, "Returning tuple.");
						node->js.ps.ps_TupFromTlist =
							(isDone == ExprMultipleResult);
						return result;
					}
				}

				/*
				 * If we didn't return a tuple, set NeedNew and flip the probe-build relation.
				 */
				elog(INFO, "Did not return a tuple.");
				if (node->js.jointype == JOIN_IN)
				{
					elog(INFO, "Need to fetch more.");
					node->hj_NeedNew = true;
					node->hj_FromInner = !node->hj_FromInner;
					break;		/* out of loop over hash bucket */
				}
			}
		}
	}
}

/* ----------------------------------------------------------------
 *		ExecInitHashJoin
 *
 *		Init routine for HashJoin node.
 * ----------------------------------------------------------------
 */
HashJoinState *
ExecInitHashJoin(HashJoin *node, EState *estate)
{
	HashJoinState *hjstate;
	Hash	   *outerNode;
	Hash	   *innerNode;
	List	   *lclauses;
	List	   *rclauses;
	List	   *hoperators;
	ListCell   *l;

	elog(INFO, "Initiating hash join");

	/*
	 * create state structure
	 */
	elog(INFO, "Creating state structure");
	hjstate = makeNode(HashJoinState);
	hjstate->js.ps.plan = (Plan *) node;
	hjstate->js.ps.state = estate;

	/*
	 * Miscellaneous initialization
	 *
	 * create expression context for node
	 */
	ExecAssignExprContext(estate, &hjstate->js.ps);

	/*
	 * initialize child expressions
	 */
	elog(INFO, "Initializing child expressions");
	elog(INFO, "Initializing target list");
	hjstate->js.ps.targetlist = (List *)
		ExecInitExpr((Expr *) node->join.plan.targetlist,
					 (PlanState *) hjstate);
	elog(INFO, "Initializing qualifiers");
	hjstate->js.ps.qual = (List *)
		ExecInitExpr((Expr *) node->join.plan.qual,
					 (PlanState *) hjstate);
	elog(INFO, "Initializing join type");
	hjstate->js.jointype = node->join.jointype;
	elog(INFO, "Initializing join qualifiers");
	hjstate->js.joinqual = (List *)
		ExecInitExpr((Expr *) node->join.joinqual,
					 (PlanState *) hjstate);
	elog(INFO, "Initializing hash clauses");
	hjstate->hashclauses = (List *)
		ExecInitExpr((Expr *) node->hashclauses,
					 (PlanState *) hjstate);

	/*
	 * initialize child nodes
	 */
	elog(INFO, "Initializing child nodes");
	outerNode = (Hash *) outerPlan(node);
	innerNode = (Hash *) innerPlan(node);

	outerPlanState(hjstate) = ExecInitNode((Plan *) outerNode, estate);
	innerPlanState(hjstate) = ExecInitNode((Plan *) innerNode, estate);

#define HASHJOIN_NSLOTS 3

	/*
	 * tuple table initialization
	 */
	elog(INFO, "Initializing tuple tables");
	ExecInitResultTupleSlot(estate, &hjstate->js.ps);
	hjstate->hj_OuterTupleSlot = ExecInitExtraTupleSlot(estate);

	switch (node->join.jointype)
	{
		case JOIN_INNER:
		case JOIN_IN:
			elog(INFO, "inner join");
			break;
		case JOIN_LEFT:
			elog(INFO, "left join");
			hjstate->hj_NullInnerTupleSlot =
				ExecInitNullTupleSlot(estate,
								 ExecGetResultType(innerPlanState(hjstate)));
			break;
		default:
			elog(ERROR, "unrecognized join type: %d",
				 (int) node->join.jointype);
			break;
	}

	/*
	 * now for some voodoo.  our temporary tuple slot is actually the result
	 * tuple slot of the Hash node (which is our inner plan).  we do this
	 * because Hash nodes don't return tuples via ExecProcNode() -- instead
	 * the hash join node uses ExecScanHashBucket() to get at the contents of
	 * the hash table.	-cim 6/9/91
	 */
	elog(INFO, "voodoo block");
	{
		HashState  *hashstate = (HashState *) innerPlanState(hjstate);
		TupleTableSlot *slot = hashstate->ps.ps_ResultTupleSlot;

		hjstate->hj_InnerTupleSlot = slot;
	}

	/*
	 * initialize tuple type and projection info
	 */
	elog(INFO, "Initializing tuple type");
	ExecAssignResultTypeFromTL(&hjstate->js.ps);
	elog(INFO, "Initializing projection info");
	ExecAssignProjectionInfo(&hjstate->js.ps);

	elog(INFO, "Initializing slot descriptors.");
	elog(INFO, "Outer plan state is %X", outerPlanState(hjstate));
	ExecSetSlotDescriptor(hjstate->hj_OuterTupleSlot,
						  ExecGetResultType(outerPlanState(hjstate)),
						  false);
	elog(INFO, "Inner plan state is %X", innerPlanState(hjstate));
	ExecSetSlotDescriptor(hjstate->hj_InnerTupleSlot,
						  ExecGetResultType(innerPlanState(hjstate)),
						  false);

	/*
	 * initialize hash-specific info
	 */
	elog(INFO, "Initializing hash-state info");
	hjstate->hj_InnerTable = NULL;
	hjstate->hj_OuterTable = NULL;
	hjstate->hj_FirstOuterTupleSlot = NULL;

	hjstate->hj_CurHashValue = 0;
	hjstate->hj_CurBucketNo = 0;
	hjstate->hj_CurTuple = NULL;

	/*
	 * Deconstruct the hash clauses into outer and inner argument values, so
	 * that we can evaluate those subexpressions separately.  Also make a list
	 * of the hash operator OIDs, in preparation for looking up the hash
	 * functions to use.
	 */
	elog(INFO, "Deconstructing hash clauses");
	lclauses = NIL;
	rclauses = NIL;
	hoperators = NIL;
	foreach(l, hjstate->hashclauses)
	{
		FuncExprState *fstate = (FuncExprState *) lfirst(l);
		OpExpr	   *hclause;

		Assert(IsA(fstate, FuncExprState));
		hclause = (OpExpr *) fstate->xprstate.expr;
		Assert(IsA(hclause, OpExpr));
		lclauses = lappend(lclauses, linitial(fstate->args));
		rclauses = lappend(rclauses, lsecond(fstate->args));
		hoperators = lappend_oid(hoperators, hclause->opno);
	}
	elog(INFO, "Initializing hash clauses");
	hjstate->hj_OuterHashKeys = lclauses;
	hjstate->hj_InnerHashKeys = rclauses;
	hjstate->hj_HashOperators = hoperators;
	/* child Hash node needs to evaluate inner hash keys, too */
	((HashState *) innerPlanState(hjstate))->hashkeys = rclauses;

	hjstate->js.ps.ps_OuterTupleSlot = NULL;
	hjstate->js.ps.ps_TupFromTlist = false;
	hjstate->hj_NeedNew = true;
	hjstate->hj_MatchedTuple = false;
	hjstate->hj_InnerNotEmpty = false;
	hjstate->hj_OuterNotEmpty = false;

	elog(INFO, "Initialization complete.");
	return hjstate;
}

int
ExecCountSlotsHashJoin(HashJoin *node)
{
	return ExecCountSlotsNode(outerPlan(node)) +
		ExecCountSlotsNode(innerPlan(node)) +
		HASHJOIN_NSLOTS;
}

/* ----------------------------------------------------------------
 *		ExecEndHashJoin
 *
 *		clean up routine for HashJoin node
 * ----------------------------------------------------------------
 */
void
ExecEndHashJoin(HashJoinState *node)
{
	/*
	 * Free hash table
	 */
	if (node->hj_InnerTable)
	{
		ExecHashTableDestroy(node->hj_InnerTable);
		node->hj_InnerTable = NULL;
	}

	/*
	 * Free the exprcontext
	 */
	ExecFreeExprContext(&node->js.ps);

	/*
	 * clean out the tuple table
	 */
	ExecClearTuple(node->js.ps.ps_ResultTupleSlot);
	ExecClearTuple(node->hj_OuterTupleSlot);
	ExecClearTuple(node->hj_InnerTupleSlot);

	/*
	 * clean up subtrees
	 */
	ExecEndNode(outerPlanState(node));
	ExecEndNode(innerPlanState(node));
}

/*
 * ExecHashJoinOuterGetTuple
 *
 *		get the next outer tuple for hashjoin: either by
 *		executing a plan node in the first pass, or from
 *		the temp files for the hashjoin batches.
 *
 * Returns a null slot if no more outer tuples.  On success, the tuple's
 * hash value is stored at *hashvalue --- this is either originally computed,
 * or re-read from the temp file.
 */
static TupleTableSlot *
ExecHashJoinOuterGetTuple(HashState *outerNode,
						  HashJoinState *hjstate,
						  uint32 *hashvalue)
{
	/*
	 * Decide which hash table we're probing at.
	 */
	HashJoinTable hashtable = hjstate->hj_FromInner ? hjstate->hj_OuterTable : hjstate->hj_InnerTable;
	int			curbatch = hashtable->curbatch;
	TupleTableSlot *slot;

	if (curbatch == 0)
	{							/* if it is the first pass */

		/*
		 * Check to see if first outer tuple was already fetched by
		 * ExecHashJoin() and not used yet.
		 */
		slot = hjstate->hj_FirstOuterTupleSlot;
		if (!TupIsNull(slot))
			hjstate->hj_FirstOuterTupleSlot = NULL;
		else
			slot = ExecProcNode(outerNode);
		if (!TupIsNull(slot))
		{
			/*
			 * We have to compute the tuple's hash value.
			 */
			ExprContext *econtext = hjstate->js.ps.ps_ExprContext;

			if (hjstate->hj_FromInner)
				econtext->ecxt_outertuple = slot;
			else
				econtext->ecxt_innertuple = slot;

			*hashvalue = ExecHashGetHashValue(hashtable, econtext,
											  hjstate->hj_FromInner ? hjstate->hj_OuterHashKeys : hjstate->hj_InnerHashKeys);

			/* remember probe relation is not empty for possible rescan */
			if (hjstate->hj_FromInner)
				hjstate->hj_InnerNotEmpty = true;
			else 
				hjstate->hj_OuterNotEmpty = true;

			return slot;
		}
	}
	return NULL;
}

/*
 * ExecHashJoinNewBatch
 *		switch to a new hashjoin batch
 *
 * Returns the number of the new batch (1..nbatch-1), or nbatch if no more.
 * We will never return a batch number that has an empty outer batch file.
 * ------------------------------------------------------------------------
 * CS448
 * 
 * Batch hashes are disabled as per assignment specification.
 * ------------------------------------------------------------------------
 */
static int
ExecHashJoinNewBatch(HashJoinState *hjstate)
{
	return 0;
}

/*
 * ExecHashJoinSaveTuple
 *		save a tuple to a batch file.
 *
 * The data recorded in the file for each tuple is its hash value,
 * then an image of its HeapTupleData (with meaningless t_data pointer)
 * followed by the HeapTupleHeader and tuple data.
 *
 * Note: it is important always to call this in the regular executor
 * context, not in a shorter-lived context; else the temp file buffers
 * will get messed up.
 */
void
ExecHashJoinSaveTuple(HeapTuple heapTuple, uint32 hashvalue,
					  BufFile **fileptr)
{
	BufFile    *file = *fileptr;
	size_t		written;

	if (file == NULL)
	{
		/* First write to this batch file, so open it. */
		file = BufFileCreateTemp(false);
		*fileptr = file;
	}

	written = BufFileWrite(file, (void *) &hashvalue, sizeof(uint32));
	if (written != sizeof(uint32))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to hash-join temporary file: %m")));

	written = BufFileWrite(file, (void *) heapTuple, sizeof(HeapTupleData));
	if (written != sizeof(HeapTupleData))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to hash-join temporary file: %m")));

	written = BufFileWrite(file, (void *) heapTuple->t_data, heapTuple->t_len);
	if (written != (size_t) heapTuple->t_len)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to hash-join temporary file: %m")));
}

/*
 * ExecHashJoinGetSavedTuple
 *		read the next tuple from a batch file.	Return NULL if no more.
 *
 * On success, *hashvalue is set to the tuple's hash value, and the tuple
 * itself is stored in the given slot.
 */
static TupleTableSlot *
ExecHashJoinGetSavedTuple(HashJoinState *hjstate,
						  BufFile *file,
						  uint32 *hashvalue,
						  TupleTableSlot *tupleSlot)
{
	HeapTupleData htup;
	size_t		nread;
	HeapTuple	heapTuple;

	nread = BufFileRead(file, (void *) hashvalue, sizeof(uint32));
	if (nread == 0)
		return NULL;			/* end of file */
	if (nread != sizeof(uint32))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from hash-join temporary file: %m")));
	nread = BufFileRead(file, (void *) &htup, sizeof(HeapTupleData));
	if (nread != sizeof(HeapTupleData))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from hash-join temporary file: %m")));
	heapTuple = palloc(HEAPTUPLESIZE + htup.t_len);
	memcpy((char *) heapTuple, (char *) &htup, sizeof(HeapTupleData));
	heapTuple->t_datamcxt = CurrentMemoryContext;
	heapTuple->t_data = (HeapTupleHeader)
		((char *) heapTuple + HEAPTUPLESIZE);
	nread = BufFileRead(file, (void *) heapTuple->t_data, htup.t_len);
	if (nread != (size_t) htup.t_len)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from hash-join temporary file: %m")));
	return ExecStoreTuple(heapTuple, tupleSlot, InvalidBuffer, true);
}


void
ExecReScanHashJoin(HashJoinState *node, ExprContext *exprCtxt)
{
	/*
	 * CS448
	 * 
	 * Rescans are disabled.
	 */
}
