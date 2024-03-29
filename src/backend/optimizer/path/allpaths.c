/*-------------------------------------------------------------------------
 *
 * allpaths.c
 *	  Routines to find possible search paths for processing a query
 *
 * Portions Copyright (c) 1996-2005, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  $PostgreSQL: pgsql/src/backend/optimizer/path/allpaths.c,v 1.137.2.3 2006/05/02 04:34:24 tgl Exp $
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"
#include "nodes/makefuncs.h"
#include "nodes/print.h"
#include "optimizer/clauses.h"
#include "optimizer/cost.h"
#include "optimizer/geqo.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/plancat.h"
#include "optimizer/planner.h"
#include "optimizer/predtest.h"
#include "optimizer/prep.h"
#include "optimizer/var.h"
#include "parser/parsetree.h"
#include "parser/parse_clause.h"
#include "parser/parse_expr.h"
#include "rewrite/rewriteManip.h"

/* These parameters are set by GUC */
bool		constraint_exclusion = false;
bool		enable_geqo = false;	/* just in case GUC doesn't set it */
int			geqo_threshold;


static void set_base_rel_pathlists(PlannerInfo *root);
static void set_plain_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
					   RangeTblEntry *rte);
static void set_inherited_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
						   Index rti, RangeTblEntry *rte,
						   List *inheritlist);
static void set_subquery_pathlist(PlannerInfo *root, RelOptInfo *rel,
					  Index rti, RangeTblEntry *rte);
static void set_function_pathlist(PlannerInfo *root, RelOptInfo *rel,
					  RangeTblEntry *rte);
static RelOptInfo *make_one_rel_by_joins(PlannerInfo *root, int levels_needed,
					  List *initial_rels);
static bool subquery_is_pushdown_safe(Query *subquery, Query *topquery,
						  bool *differentTypes);
static bool recurse_pushdown_safe(Node *setOp, Query *topquery,
					  bool *differentTypes);
static void compare_tlist_datatypes(List *tlist, List *colTypes,
						bool *differentTypes);
static bool qual_is_pushdown_safe(Query *subquery, Index rti, Node *qual,
					  bool *differentTypes);
static void subquery_push_qual(Query *subquery,
				   RangeTblEntry *rte, Index rti, Node *qual);
static void recurse_push_qual(Node *setOp, Query *topquery,
				  RangeTblEntry *rte, Index rti, Node *qual);

static void print_relids(Relids relids);
static void print_restrictclauses(PlannerInfo *root, List *clauses);
static void print_path(PlannerInfo *root, Path *path, int indent);
void debug_print_rel(PlannerInfo *root, RelOptInfo *rel);

/*
 * make_one_rel
 *	  Finds all possible access paths for executing a query, returning a
 *	  single rel that represents the join of all base rels in the query.
 */
RelOptInfo *
make_one_rel(PlannerInfo *root)
{
	RelOptInfo *rel;

	/*
	 * Generate access paths for the base rels.
	 */
	set_base_rel_pathlists(root);

	/*
	 * Generate access paths for the entire join tree.
	 */
	Assert(root->parse->jointree != NULL &&
		   IsA(root->parse->jointree, FromExpr));

	rel = make_fromexpr_rel(root, root->parse->jointree);

	/*
	 * The result should join all and only the query's base rels.
	 */
#ifdef USE_ASSERT_CHECKING
	{
		int			num_base_rels = 0;
		Index		rti;

		for (rti = 1; rti < root->base_rel_array_size; rti++)
		{
			RelOptInfo *brel = root->base_rel_array[rti];

			if (brel == NULL)
				continue;

			Assert(brel->relid == rti); /* sanity check on array */

			/* ignore RTEs that are "other rels" */
			if (brel->reloptkind != RELOPT_BASEREL)
				continue;

			Assert(bms_is_member(rti, rel->relids));
			num_base_rels++;
		}

		Assert(bms_num_members(rel->relids) == num_base_rels);
	}
#endif

	return rel;
}

/*
 * set_base_rel_pathlists
 *	  Finds all paths available for scanning each base-relation entry.
 *	  Sequential scan and any available indices are considered.
 *	  Each useful path is attached to its relation's 'pathlist' field.
 */
static void
set_base_rel_pathlists(PlannerInfo *root)
{
	Index		rti;

	if (root->sort_pathkeys == NULL) {
		printf("CS448 **** Interesting Order from Order By clauses: ()\n");
	} else {
		printf("CS448 **** Interesting Order from Order By clauses: ");
		print_pathkeys(root->sort_pathkeys, root->parse->rtable);
	}
	if (root->group_pathkeys == NULL) {
		printf("CS448 **** Interesting Order from Group By clauses: ()\n");
	} else {
		printf("CS448 **** Interesting Order from Group By clauses: ");
		print_pathkeys(root->group_pathkeys, root->parse->rtable);
	}
	if (root->hasJoinRTEs) {
		printf("CS448 **** Interesting Order from Join predicates: ()\n");
	} else {
		/*
		 * This thing has joins.
		 * Build pathkey lists for these joins.
		 */
		printf("CS448 **** Interesting Order from Join predicates: ");
		print_pathkeys(root->equi_key_list, root->parse->rtable);
	}

	/*
	 * Note: because we call expand_inherited_rtentry inside the loop, it's
	 * quite possible for the base_rel_array to be enlarged while the loop
	 * runs.  Hence don't try to optimize the loop.
	 */
	for (rti = 1; rti < root->base_rel_array_size; rti++)
	{
		RelOptInfo *rel = root->base_rel_array[rti];
		RangeTblEntry *rte;
		List	   *inheritlist;

		/* there may be empty slots corresponding to non-baserel RTEs */
		if (rel == NULL)
			continue;

		Assert(rel->relid == rti);		/* sanity check on array */

		/* ignore RTEs that are "other rels" */
		if (rel->reloptkind != RELOPT_BASEREL)
			continue;

		rte = rt_fetch(rti, root->parse->rtable);

		if (rel->rtekind == RTE_SUBQUERY)
		{
			/* Subquery --- generate a separate plan for it */
			set_subquery_pathlist(root, rel, rti, rte);
		}
		else if (rel->rtekind == RTE_FUNCTION)
		{
			/* RangeFunction --- generate a separate plan for it */
			set_function_pathlist(root, rel, rte);
		}
		else if ((inheritlist = expand_inherited_rtentry(root, rti)) != NIL)
		{
			/* Relation is root of an inheritance tree, process specially */
			set_inherited_rel_pathlist(root, rel, rti, rte, inheritlist);
		}
		else
		{
			/* Plain relation */
			printf("Possible Paths for Relation %u:\n", rti);
			set_plain_rel_pathlist(root, rel, rte);
		}

#ifdef OPTIMIZER_DEBUG
		debug_print_rel(root, rel);
#endif
	}
}

/*
 * set_plain_rel_pathlist
 *	  Build access paths for a plain relation (no subquery, no inheritance)
 */
static void
set_plain_rel_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	ListCell   *l, *i, *k;

	/* Mark rel with estimated output rows, width, etc */
	set_baserel_size_estimates(root, rel);

	/* Test any partial indexes of rel for applicability */
	check_partial_indexes(root, rel);

	/*
	 * Check to see if we can extract any restriction conditions from join
	 * quals that are OR-of-AND structures.  If so, add them to the rel's
	 * restriction list, and recompute the size estimates.
	 */
	if (create_or_index_quals(root, rel))
		set_baserel_size_estimates(root, rel);

	/*
	 * Generate paths and add them to the rel's pathlist.
	 *
	 * Note: add_path() will discard any paths that are dominated by another
	 * available path, keeping only those paths that are superior along at
	 * least one dimension of cost or sortedness.
	 */

	/* Consider sequential scan */
	add_path(rel, create_seqscan_path(root, rel));

	/* build one for each pathkey in the group by or order by clauses */
	foreach (i, root->query_pathkeys) {
		/* Filter out the relation that does not have the pathkey specified */
		List *pathkey = (List *) lfirst(i);
		foreach (k, pathkey)
		{
			PathKeyItem *item = (PathKeyItem *) lfirst(k);
			Var		   *var = (Var *) item->key;
			RangeTblEntry *rte;

			Assert(var->varno > 0 &&
				   (int) var->varno <= list_length(root->parse->rtable));
			rte = rt_fetch(var->varno, root->parse->rtable);
			if (var->varno == rel->relid) {
				add_path(rel, create_sorted_seqscan_path(root, rel, i));
			}
		}
	}
	/* build one for each pathkey in the equi-key list for joins */
	foreach (i, root->equi_key_list) {
		List *pathkey = (List *) lfirst(i);
		int should_add = 0, key_count = 0;
		foreach (k, pathkey)
		{
			PathKeyItem *item = (PathKeyItem *) lfirst(k);
			Var		   *var = (Var *) item->key;
			RangeTblEntry *rte;

			Assert(var->varno > 0 &&
				   (int) var->varno <= list_length(root->parse->rtable));
			rte = rt_fetch(var->varno, root->parse->rtable);
			if (var->varno == rel->relid) {
				should_add = 1;
			}
			key_count += 1;
		}
		if (should_add == 1 && key_count > 1) {
			add_path(rel, create_sorted_seqscan_path(root, rel, i));
		}
	}
	foreach(l, rel->pathlist) print_path(root, lfirst(l), 1);

	/* Consider index scans */
	create_index_paths(root, rel);

	/* Consider TID scans */
	create_tidscan_paths(root, rel);

	/* Now find the cheapest of the paths for this rel */
	set_cheapest(rel);
	printf("\n");
}

/*
 * set_inherited_rel_pathlist
 *	  Build access paths for a inheritance tree rooted at rel
 *
 * inheritlist is a list of RT indexes of all tables in the inheritance tree,
 * including a duplicate of the parent itself.	Note we will not come here
 * unless there's at least one child in addition to the parent.
 *
 * NOTE: the passed-in rel and RTE will henceforth represent the appended
 * result of the whole inheritance tree.  The members of inheritlist represent
 * the individual tables --- in particular, the inheritlist member that is a
 * duplicate of the parent RTE represents the parent table alone.
 * We will generate plans to scan the individual tables that refer to
 * the inheritlist RTEs, whereas Vars elsewhere in the plan tree that
 * refer to the original RTE are taken to refer to the append output.
 * In particular, this means we have separate RelOptInfos for the parent
 * table and for the append output, which is a good thing because they're
 * not the same size.
 */
static void
set_inherited_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
						   Index rti, RangeTblEntry *rte,
						   List *inheritlist)
{
	int			parentRTindex = rti;
	Oid			parentOID = rte->relid;
	List	   *subpaths = NIL;
	ListCell   *il;

	/*
	 * XXX for now, can't handle inherited expansion of FOR UPDATE/SHARE; can
	 * we do better?
	 */
	if (list_member_int(root->parse->rowMarks, parentRTindex))
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("SELECT FOR UPDATE/SHARE is not supported for inheritance queries")));

	/*
	 * We might have looked up indexes for the parent rel, but they're
	 * really not relevant to the appendrel.  Reset the pointer to avoid
	 * any confusion.
	 */
	rel->indexlist = NIL;

	/*
	 * Initialize to compute size estimates for whole inheritance tree
	 */
	rel->rows = 0;
	rel->width = 0;

	/*
	 * Generate access paths for each table in the tree (parent AND children),
	 * and pick the cheapest path for each table.
	 */
	foreach(il, inheritlist)
	{
		int			childRTindex = lfirst_int(il);
		RangeTblEntry *childrte;
		Oid			childOID;
		RelOptInfo *childrel;
		ListCell   *parentvars;
		ListCell   *childvars;

		childrte = rt_fetch(childRTindex, root->parse->rtable);
		childOID = childrte->relid;

		/*
		 * Make a RelOptInfo for the child so we can do planning. Mark it as
		 * an "other rel" since it will not be part of the main join tree.
		 */
		childrel = build_other_rel(root, childRTindex);

		/*
		 * Copy the parent's targetlist and restriction quals to the child,
		 * with attribute-number adjustment as needed.	We don't bother to
		 * copy the join quals, since we can't do any joining of the
		 * individual tables.  Also, we just zap attr_needed rather than
		 * trying to adjust it; it won't be looked at in the child.
		 */
		childrel->reltargetlist = (List *)
			adjust_inherited_attrs((Node *) rel->reltargetlist,
								   parentRTindex,
								   parentOID,
								   childRTindex,
								   childOID);
		childrel->attr_needed = NULL;
		childrel->baserestrictinfo = (List *)
			adjust_inherited_attrs((Node *) rel->baserestrictinfo,
								   parentRTindex,
								   parentOID,
								   childRTindex,
								   childOID);

		/*
		 * If we can prove we don't need to scan this child via constraint
		 * exclusion, just ignore it.  (We have to have converted the
		 * baserestrictinfo Vars before we can make the test.)
		 */
		if (constraint_exclusion)
		{
			List	   *constraint_pred;

			constraint_pred = get_relation_constraints(childOID, childrel);

			/*
			 * We do not currently enforce that CHECK constraints contain only
			 * immutable functions, so it's necessary to check here. We
			 * daren't draw conclusions from plan-time evaluation of
			 * non-immutable functions.
			 */
			if (!contain_mutable_functions((Node *) constraint_pred))
			{
				/*
				 * The constraints are effectively ANDed together, so we can
				 * just try to refute the entire collection at once.  This may
				 * allow us to make proofs that would fail if we took them
				 * individually.
				 */
				if (predicate_refuted_by(constraint_pred,
										 childrel->baserestrictinfo))
					continue;
			}
		}

		/*
		 * Compute the child's access paths, and save the cheapest.
		 */
		set_plain_rel_pathlist(root, childrel, childrte);

		subpaths = lappend(subpaths, childrel->cheapest_total_path);

		/*
		 * Propagate size information from the child back to the parent. For
		 * simplicity, we use the largest widths from any child as the parent
		 * estimates.
		 */
		rel->rows += childrel->rows;
		if (childrel->width > rel->width)
			rel->width = childrel->width;

		forboth(parentvars, rel->reltargetlist,
				childvars, childrel->reltargetlist)
		{
			Var		   *parentvar = (Var *) lfirst(parentvars);
			Var		   *childvar = (Var *) lfirst(childvars);

			if (IsA(parentvar, Var) &&IsA(childvar, Var))
			{
				int			pndx = parentvar->varattno - rel->min_attr;
				int			cndx = childvar->varattno - childrel->min_attr;

				if (childrel->attr_widths[cndx] > rel->attr_widths[pndx])
					rel->attr_widths[pndx] = childrel->attr_widths[cndx];
			}
		}
	}

	/*
	 * Finally, build Append path and install it as the only access path for
	 * the parent rel.	(Note: this is correct even if we have zero or one
	 * live subpath due to constraint exclusion.)
	 */
	add_path(rel, (Path *) create_append_path(rel, subpaths));

	/* Select cheapest path (pretty easy in this case...) */
	set_cheapest(rel);
}

/* quick-and-dirty test to see if any joining is needed */
static bool
has_multiple_baserels(PlannerInfo *root)
{
	int			num_base_rels = 0;
	Index		rti;

	for (rti = 1; rti < root->base_rel_array_size; rti++)
	{
		RelOptInfo *brel = root->base_rel_array[rti];

		if (brel == NULL)
			continue;

		/* ignore RTEs that are "other rels" */
		if (brel->reloptkind == RELOPT_BASEREL)
			if (++num_base_rels > 1)
				return true;
	}
	return false;
}

/*
 * set_subquery_pathlist
 *		Build the (single) access path for a subquery RTE
 */
static void
set_subquery_pathlist(PlannerInfo *root, RelOptInfo *rel,
					  Index rti, RangeTblEntry *rte)
{
	Query	   *parse = root->parse;
	Query	   *subquery = rte->subquery;
	bool	   *differentTypes;
	double		tuple_fraction;
	List	   *pathkeys;
	List	   *subquery_pathkeys;

	/* We need a workspace for keeping track of set-op type coercions */
	differentTypes = (bool *)
		palloc0((list_length(subquery->targetList) + 1) * sizeof(bool));

	/*
	 * If there are any restriction clauses that have been attached to the
	 * subquery relation, consider pushing them down to become WHERE or HAVING
	 * quals of the subquery itself.  This transformation is useful because it
	 * may allow us to generate a better plan for the subquery than evaluating
	 * all the subquery output rows and then filtering them.
	 *
	 * There are several cases where we cannot push down clauses. Restrictions
	 * involving the subquery are checked by subquery_is_pushdown_safe().
	 * Restrictions on individual clauses are checked by
	 * qual_is_pushdown_safe().
	 *
	 * Non-pushed-down clauses will get evaluated as qpquals of the
	 * SubqueryScan node.
	 *
	 * XXX Are there any cases where we want to make a policy decision not to
	 * push down a pushable qual, because it'd result in a worse plan?
	 */
	if (rel->baserestrictinfo != NIL &&
		subquery_is_pushdown_safe(subquery, subquery, differentTypes))
	{
		/* OK to consider pushing down individual quals */
		List	   *upperrestrictlist = NIL;
		ListCell   *l;

		foreach(l, rel->baserestrictinfo)
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(l);
			Node	   *clause = (Node *) rinfo->clause;

			if (qual_is_pushdown_safe(subquery, rti, clause, differentTypes))
			{
				/* Push it down */
				subquery_push_qual(subquery, rte, rti, clause);
			}
			else
			{
				/* Keep it in the upper query */
				upperrestrictlist = lappend(upperrestrictlist, rinfo);
			}
		}
		rel->baserestrictinfo = upperrestrictlist;
	}

	pfree(differentTypes);

	/*
	 * We can safely pass the outer tuple_fraction down to the subquery if the
	 * outer level has no joining, aggregation, or sorting to do. Otherwise
	 * we'd better tell the subquery to plan for full retrieval. (XXX This
	 * could probably be made more intelligent ...)
	 */
	if (parse->hasAggs ||
		parse->groupClause ||
		parse->havingQual ||
		parse->distinctClause ||
		parse->sortClause ||
		has_multiple_baserels(root))
		tuple_fraction = 0.0;	/* default case */
	else
		tuple_fraction = root->tuple_fraction;

	/* Generate the plan for the subquery */
	rel->subplan = subquery_planner(subquery, tuple_fraction,
									&subquery_pathkeys);

	/* Copy number of output rows from subplan */
	rel->tuples = rel->subplan->plan_rows;

	/* Mark rel with estimated output rows, width, etc */
	set_baserel_size_estimates(root, rel);

	/* Convert subquery pathkeys to outer representation */
	pathkeys = convert_subquery_pathkeys(root, rel, subquery_pathkeys);

	/* Generate appropriate path */
	add_path(rel, create_subqueryscan_path(rel, pathkeys));

	/* Select cheapest path (pretty easy in this case...) */
	set_cheapest(rel);
}

/*
 * set_function_pathlist
 *		Build the (single) access path for a function RTE
 */
static void
set_function_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	/* Mark rel with estimated output rows, width, etc */
	set_function_size_estimates(root, rel);

	/* Generate appropriate path */
	add_path(rel, create_functionscan_path(root, rel));

	/* Select cheapest path (pretty easy in this case...) */
	set_cheapest(rel);
}

/*
 * make_fromexpr_rel
 *	  Build access paths for a FromExpr jointree node.
 */
RelOptInfo *
make_fromexpr_rel(PlannerInfo *root, FromExpr *from)
{
	int			levels_needed;
	List	   *initial_rels = NIL;
	ListCell   *jt;

	/*
	 * Count the number of child jointree nodes.  This is the depth of the
	 * dynamic-programming algorithm we must employ to consider all ways of
	 * joining the child nodes.
	 */
	levels_needed = list_length(from->fromlist);

	if (levels_needed <= 0)
		return NULL;			/* nothing to do? */

	/*
	 * Construct a list of rels corresponding to the child jointree nodes.
	 * This may contain both base rels and rels constructed according to
	 * explicit JOIN directives.
	 */
	foreach(jt, from->fromlist)
	{
		Node	   *jtnode = (Node *) lfirst(jt);

		initial_rels = lappend(initial_rels,
							   make_jointree_rel(root, jtnode));
	}

	if (levels_needed == 1)
	{
		/*
		 * Single jointree node, so we're done.
		 */
		return (RelOptInfo *) linitial(initial_rels);
	}
	else
	{
		/*
		 * Consider the different orders in which we could join the rels,
		 * using either GEQO or regular optimizer.
		 */
		if (enable_geqo && levels_needed >= geqo_threshold)
			return geqo(root, levels_needed, initial_rels);
		else
			return make_one_rel_by_joins(root, levels_needed, initial_rels);
	}
}

/*
 * make_one_rel_by_joins
 *	  Find all possible joinpaths for a query by successively finding ways
 *	  to join component relations into join relations.
 *
 * 'levels_needed' is the number of iterations needed, ie, the number of
 *		independent jointree items in the query.  This is > 1.
 *
 * 'initial_rels' is a list of RelOptInfo nodes for each independent
 *		jointree item.	These are the components to be joined together.
 *
 * Returns the final level of join relations, i.e., the relation that is
 * the result of joining all the original relations together.
 */
static RelOptInfo *
make_one_rel_by_joins(PlannerInfo *root, int levels_needed, List *initial_rels)
{
	List	  **joinitems;
	int			lev;
	RelOptInfo *rel;

	/*
	 * We employ a simple "dynamic programming" algorithm: we first find all
	 * ways to build joins of two jointree items, then all ways to build joins
	 * of three items (from two-item joins and single items), then four-item
	 * joins, and so on until we have considered all ways to join all the
	 * items into one rel.
	 *
	 * joinitems[j] is a list of all the j-item rels.  Initially we set
	 * joinitems[1] to represent all the single-jointree-item relations.
	 */
	joinitems = (List **) palloc0((levels_needed + 1) * sizeof(List *));

	joinitems[1] = initial_rels;

	for (lev = 2; lev <= levels_needed; lev++)
	{
		ListCell   *x;

		/*
		 * Determine all possible pairs of relations to be joined at this
		 * level, and build paths for making each one from every available
		 * pair of lower-level relations.
		 */
		joinitems[lev] = make_rels_by_joins(root, lev, joinitems);

		/*
		 * Do cleanup work on each just-processed rel.
		 */
		foreach(x, joinitems[lev])
		{
			rel = (RelOptInfo *) lfirst(x);

			/* Find and save the cheapest paths for this rel */
			set_cheapest(rel);

#ifdef OPTIMIZER_DEBUG
			debug_print_rel(root, rel);
#endif
		}
	}

	/*
	 * We should have a single rel at the final level.
	 */
	if (joinitems[levels_needed] == NIL)
		elog(ERROR, "failed to build any %d-way joins", levels_needed);
	Assert(list_length(joinitems[levels_needed]) == 1);

	rel = (RelOptInfo *) linitial(joinitems[levels_needed]);

	return rel;
}

/*****************************************************************************
 *			PUSHING QUALS DOWN INTO SUBQUERIES
 *****************************************************************************/

/*
 * subquery_is_pushdown_safe - is a subquery safe for pushing down quals?
 *
 * subquery is the particular component query being checked.  topquery
 * is the top component of a set-operations tree (the same Query if no
 * set-op is involved).
 *
 * Conditions checked here:
 *
 * 1. If the subquery has a LIMIT clause, we must not push down any quals,
 * since that could change the set of rows returned.
 *
 * 2. If the subquery contains EXCEPT or EXCEPT ALL set ops we cannot push
 * quals into it, because that would change the results.
 *
 * 3. For subqueries using UNION/UNION ALL/INTERSECT/INTERSECT ALL, we can
 * push quals into each component query, but the quals can only reference
 * subquery columns that suffer no type coercions in the set operation.
 * Otherwise there are possible semantic gotchas.  So, we check the
 * component queries to see if any of them have different output types;
 * differentTypes[k] is set true if column k has different type in any
 * component.
 */
static bool
subquery_is_pushdown_safe(Query *subquery, Query *topquery,
						  bool *differentTypes)
{
	SetOperationStmt *topop;

	/* Check point 1 */
	if (subquery->limitOffset != NULL || subquery->limitCount != NULL)
		return false;

	/* Are we at top level, or looking at a setop component? */
	if (subquery == topquery)
	{
		/* Top level, so check any component queries */
		if (subquery->setOperations != NULL)
			if (!recurse_pushdown_safe(subquery->setOperations, topquery,
									   differentTypes))
				return false;
	}
	else
	{
		/* Setop component must not have more components (too weird) */
		if (subquery->setOperations != NULL)
			return false;
		/* Check whether setop component output types match top level */
		topop = (SetOperationStmt *) topquery->setOperations;
		Assert(topop && IsA(topop, SetOperationStmt));
		compare_tlist_datatypes(subquery->targetList,
								topop->colTypes,
								differentTypes);
	}
	return true;
}

/*
 * Helper routine to recurse through setOperations tree
 */
static bool
recurse_pushdown_safe(Node *setOp, Query *topquery,
					  bool *differentTypes)
{
	if (IsA(setOp, RangeTblRef))
	{
		RangeTblRef *rtr = (RangeTblRef *) setOp;
		RangeTblEntry *rte = rt_fetch(rtr->rtindex, topquery->rtable);
		Query	   *subquery = rte->subquery;

		Assert(subquery != NULL);
		return subquery_is_pushdown_safe(subquery, topquery, differentTypes);
	}
	else if (IsA(setOp, SetOperationStmt))
	{
		SetOperationStmt *op = (SetOperationStmt *) setOp;

		/* EXCEPT is no good */
		if (op->op == SETOP_EXCEPT)
			return false;
		/* Else recurse */
		if (!recurse_pushdown_safe(op->larg, topquery, differentTypes))
			return false;
		if (!recurse_pushdown_safe(op->rarg, topquery, differentTypes))
			return false;
	}
	else
	{
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(setOp));
	}
	return true;
}

/*
 * Compare tlist's datatypes against the list of set-operation result types.
 * For any items that are different, mark the appropriate element of
 * differentTypes[] to show that this column will have type conversions.
 */
static void
compare_tlist_datatypes(List *tlist, List *colTypes,
						bool *differentTypes)
{
	ListCell   *l;
	ListCell   *colType = list_head(colTypes);

	foreach(l, tlist)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(l);

		if (tle->resjunk)
			continue;			/* ignore resjunk columns */
		if (colType == NULL)
			elog(ERROR, "wrong number of tlist entries");
		if (exprType((Node *) tle->expr) != lfirst_oid(colType))
			differentTypes[tle->resno] = true;
		colType = lnext(colType);
	}
	if (colType != NULL)
		elog(ERROR, "wrong number of tlist entries");
}

/*
 * qual_is_pushdown_safe - is a particular qual safe to push down?
 *
 * qual is a restriction clause applying to the given subquery (whose RTE
 * has index rti in the parent query).
 *
 * Conditions checked here:
 *
 * 1. The qual must not contain any subselects (mainly because I'm not sure
 * it will work correctly: sublinks will already have been transformed into
 * subplans in the qual, but not in the subquery).
 *
 * 2. The qual must not refer to the whole-row output of the subquery
 * (since there is no easy way to name that within the subquery itself).
 *
 * 3. The qual must not refer to any subquery output columns that were
 * found to have inconsistent types across a set operation tree by
 * subquery_is_pushdown_safe().
 *
 * 4. If the subquery uses DISTINCT ON, we must not push down any quals that
 * refer to non-DISTINCT output columns, because that could change the set
 * of rows returned.  This condition is vacuous for DISTINCT, because then
 * there are no non-DISTINCT output columns, but unfortunately it's fairly
 * expensive to tell the difference between DISTINCT and DISTINCT ON in the
 * parsetree representation.  It's cheaper to just make sure all the Vars
 * in the qual refer to DISTINCT columns.
 *
 * 5. We must not push down any quals that refer to subselect outputs that
 * return sets, else we'd introduce functions-returning-sets into the
 * subquery's WHERE/HAVING quals.
 */
static bool
qual_is_pushdown_safe(Query *subquery, Index rti, Node *qual,
					  bool *differentTypes)
{
	bool		safe = true;
	List	   *vars;
	ListCell   *vl;
	Bitmapset  *tested = NULL;

	/* Refuse subselects (point 1) */
	if (contain_subplans(qual))
		return false;

	/*
	 * Examine all Vars used in clause; since it's a restriction clause, all
	 * such Vars must refer to subselect output columns.
	 */
	vars = pull_var_clause(qual, false);
	foreach(vl, vars)
	{
		Var		   *var = (Var *) lfirst(vl);
		TargetEntry *tle;

		Assert(var->varno == rti);

		/* Check point 2 */
		if (var->varattno == 0)
		{
			safe = false;
			break;
		}

		/*
		 * We use a bitmapset to avoid testing the same attno more than once.
		 * (NB: this only works because subquery outputs can't have negative
		 * attnos.)
		 */
		if (bms_is_member(var->varattno, tested))
			continue;
		tested = bms_add_member(tested, var->varattno);

		/* Check point 3 */
		if (differentTypes[var->varattno])
		{
			safe = false;
			break;
		}

		/* Must find the tlist element referenced by the Var */
		tle = get_tle_by_resno(subquery->targetList, var->varattno);
		Assert(tle != NULL);
		Assert(!tle->resjunk);

		/* If subquery uses DISTINCT or DISTINCT ON, check point 4 */
		if (subquery->distinctClause != NIL &&
			!targetIsInSortList(tle, subquery->distinctClause))
		{
			/* non-DISTINCT column, so fail */
			safe = false;
			break;
		}

		/* Refuse functions returning sets (point 5) */
		if (expression_returns_set((Node *) tle->expr))
		{
			safe = false;
			break;
		}
	}

	list_free(vars);
	bms_free(tested);

	return safe;
}

/*
 * subquery_push_qual - push down a qual that we have determined is safe
 */
static void
subquery_push_qual(Query *subquery, RangeTblEntry *rte, Index rti, Node *qual)
{
	if (subquery->setOperations != NULL)
	{
		/* Recurse to push it separately to each component query */
		recurse_push_qual(subquery->setOperations, subquery,
						  rte, rti, qual);
	}
	else
	{
		/*
		 * We need to replace Vars in the qual (which must refer to outputs of
		 * the subquery) with copies of the subquery's targetlist expressions.
		 * Note that at this point, any uplevel Vars in the qual should have
		 * been replaced with Params, so they need no work.
		 *
		 * This step also ensures that when we are pushing into a setop tree,
		 * each component query gets its own copy of the qual.
		 */
		qual = ResolveNew(qual, rti, 0, rte,
						  subquery->targetList,
						  CMD_SELECT, 0);

		/*
		 * Now attach the qual to the proper place: normally WHERE, but if the
		 * subquery uses grouping or aggregation, put it in HAVING (since the
		 * qual really refers to the group-result rows).
		 */
		if (subquery->hasAggs || subquery->groupClause || subquery->havingQual)
			subquery->havingQual = make_and_qual(subquery->havingQual, qual);
		else
			subquery->jointree->quals =
				make_and_qual(subquery->jointree->quals, qual);

		/*
		 * We need not change the subquery's hasAggs or hasSublinks flags,
		 * since we can't be pushing down any aggregates that weren't there
		 * before, and we don't push down subselects at all.
		 */
	}
}

/*
 * Helper routine to recurse through setOperations tree
 */
static void
recurse_push_qual(Node *setOp, Query *topquery,
				  RangeTblEntry *rte, Index rti, Node *qual)
{
	if (IsA(setOp, RangeTblRef))
	{
		RangeTblRef *rtr = (RangeTblRef *) setOp;
		RangeTblEntry *subrte = rt_fetch(rtr->rtindex, topquery->rtable);
		Query	   *subquery = subrte->subquery;

		Assert(subquery != NULL);
		subquery_push_qual(subquery, rte, rti, qual);
	}
	else if (IsA(setOp, SetOperationStmt))
	{
		SetOperationStmt *op = (SetOperationStmt *) setOp;

		recurse_push_qual(op->larg, topquery, rte, rti, qual);
		recurse_push_qual(op->rarg, topquery, rte, rti, qual);
	}
	else
	{
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(setOp));
	}
}

/*****************************************************************************
 *			DEBUG SUPPORT
 *****************************************************************************/


static void
print_relids(Relids relids)
{
	Relids		tmprelids;
	int			x;
	bool		first = true;

	tmprelids = bms_copy(relids);
	while ((x = bms_first_member(tmprelids)) >= 0)
	{
		if (!first)
			printf(" ");
		printf("%d", x);
		first = false;
	}
	bms_free(tmprelids);
}

static void
print_restrictclauses(PlannerInfo *root, List *clauses)
{
	ListCell   *l;

	foreach(l, clauses)
	{
		RestrictInfo *c = lfirst(l);

		print_expr((Node *) c->clause, root->parse->rtable);
		if (lnext(l))
			printf(", ");
	}
}

static void
print_path(PlannerInfo *root, Path *path, int indent)
{
	const char *ptype;
	bool		join = false;
	Path	   *subpath = NULL;
	int			i;

	switch (nodeTag(path))
	{
		case T_Path:
			ptype = "SeqScan";
			break;
		case T_IndexPath:
			ptype = "IdxScan";
			break;
		case T_BitmapHeapPath:
			ptype = "BitmapHeapScan";
			break;
		case T_BitmapAndPath:
			ptype = "BitmapAndPath";
			break;
		case T_BitmapOrPath:
			ptype = "BitmapOrPath";
			break;
		case T_TidPath:
			ptype = "TidScan";
			break;
		case T_AppendPath:
			ptype = "Append";
			break;
		case T_ResultPath:
			ptype = "Result";
			subpath = ((ResultPath *) path)->subpath;
			break;
		case T_MaterialPath:
			ptype = "Material";
			subpath = ((MaterialPath *) path)->subpath;
			break;
		case T_UniquePath:
			ptype = "Unique";
			subpath = ((UniquePath *) path)->subpath;
			break;
		case T_NestPath:
			ptype = "NestLoop";
			join = true;
			break;
		case T_MergePath:
			ptype = "MergeJoin";
			join = true;
			break;
		case T_HashPath:
			ptype = "HashJoin";
			join = true;
			break;
		default:
			ptype = "???Path";
			break;
	}

	for (i = 0; i < indent; i++)
		printf("\t");
	printf("%s", ptype);

	if (path->parent)
	{
		printf("(");
		print_relids(path->parent->relids);
		printf(") rows=%.0f", path->parent->rows);
	}
	printf(" cost=%.2f..%.2f\n", path->startup_cost, path->total_cost);

	if (path->pathkeys)
	{
		for (i = 0; i < indent; i++)
			printf("\t");
		printf("  pathkeys: ");
		print_pathkeys(path->pathkeys, root->parse->rtable);
	}

	if (join)
	{
		JoinPath   *jp = (JoinPath *) path;

		for (i = 0; i < indent; i++)
			printf("\t");
		printf("  clauses: ");
		print_restrictclauses(root, jp->joinrestrictinfo);
		printf("\n");

		if (IsA(path, MergePath))
		{
			MergePath  *mp = (MergePath *) path;

			if (mp->outersortkeys || mp->innersortkeys)
			{
				for (i = 0; i < indent; i++)
					printf("\t");
				printf("  sortouter=%d sortinner=%d\n",
					   ((mp->outersortkeys) ? 1 : 0),
					   ((mp->innersortkeys) ? 1 : 0));
			}
		}

		print_path(root, jp->outerjoinpath, indent + 1);
		print_path(root, jp->innerjoinpath, indent + 1);
	}

	if (subpath)
		print_path(root, subpath, indent + 1);
}

void
debug_print_rel(PlannerInfo *root, RelOptInfo *rel)
{
	ListCell   *l;

	printf("RELOPTINFO (");
	print_relids(rel->relids);
	printf("): rows=%.0f width=%d\n", rel->rows, rel->width);

	if (rel->baserestrictinfo)
	{
		printf("\tbaserestrictinfo: ");
		print_restrictclauses(root, rel->baserestrictinfo);
		printf("\n");
	}

	if (rel->joininfo)
	{
		printf("\tjoininfo: ");
		print_restrictclauses(root, rel->joininfo);
		printf("\n");
	}

	printf("\tpath list:\n");
	foreach(l, rel->pathlist)
		print_path(root, lfirst(l), 1);
	printf("\n\tcheapest startup path:\n");
	print_path(root, rel->cheapest_startup_path, 1);
	printf("\n\tcheapest total path:\n");
	print_path(root, rel->cheapest_total_path, 1);
	printf("\n");
	fflush(stdout);
}
