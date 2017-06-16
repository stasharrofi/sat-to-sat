
#include "Propagator.h"
#include "core/Solver.h"
#include "AcyclicityPropagator.h"
#include <stack>

#define noACYCLICITY_DEBUG

#ifdef PROPAGATOR_DEBUG
#ifdef ACYCLICITY_DEBUG
static const char *acycPropName = "acyc";
#endif
#endif

AcyclicityPropagator::AcyclicityPropagator(Solver *S, SATGraph *G)
	: Propagator(S),
		DFSTree(G->nodeCount)
{
#ifdef PROPAGATOR_DEBUG
#ifdef ACYCLICITY_DEBUG
	debuggingEnabled = true;
	propagatorName = acycPropName;
#endif
#endif
	Graph = G;
}

bool AcyclicityPropagator::initialize()
{
	return true;
}

bool AcyclicityPropagator::isTheoryVar(Var v)
{
  return Graph->isGraphArc(v);
}

/*________________________________________________________________________
|
| propagate acyclicity
|
| Description:
|   When an arc in the graph is set to TRUE or FALSE, check for cycles
|   and infer arcs that must not hold for the graph to remain acyclic.
|
|___________________________________________________________________________*/

inline int acycFirstEnabledOutArcIndex(SATGraph *G, Solver *S, int node)
{
	SATGraph::Arc *arcs = G->getArcs(node);

	for (int i = 0; i < G->getArcCount(node); i++)
		if (S->value(arcs[i].arcLit) == l_True)
			return i;

	return G->getArcCount(node);
}

inline int acycNextEnabledOutArcIndex(SATGraph *G, Solver *S, int node, int curIndex)
{
	SATGraph::Arc *arcs = G->getArcs(node);

	for (int i = curIndex + 1; i < G->getArcCount(node); i++)
		if (S->value(arcs[i].arcLit) == l_True)
			return i;

	return G->getArcCount(node);
}

inline int acycFirstPossibleInArcIndex(SATGraph *G, Solver *S, int node)
{
	SATGraph::Arc *arcs = G->getInverseArcs(node);

	for (int i = 0; i < G->getInverseArcCount(node); i++)
		if (S->value(arcs[i].arcLit) != l_False)
			return i;

	return G->getInverseArcCount(node);
}

inline int acycNextPossibleInArcIndex(SATGraph *G, Solver *S, int node, int curIndex)
{
	SATGraph::Arc *arcs = G->getInverseArcs(node);

	for (int i = curIndex + 1; i < G->getInverseArcCount(node); i++)
		if (S->value(arcs[i].arcLit) != l_False)
			return i;

	return G->getInverseArcCount(node);
}

#define noACYCDEBUG

bool AcyclicityPropagator::propagate(Lit p)
{
	if (!Graph->isGraphArc(p)) return false; // Literal is not an arc, exit.
	if (Graph->label(p) != p) return false; // Literal is not an arc, exit.

	int arcSourceNode = Graph->sourceNode(p);
	int arcTargetNode = Graph->targetNode(p);

#ifdef ACYCDEBUG
	printf("Propagate %i (%i->%i)\n", var(p), arcSourceNode, arcTargetNode);
#endif

	auto fstOut = [this](int node) -> int { return acycFirstEnabledOutArcIndex(Graph, SolverInstance, node); };
	auto lstOut = [this](int node) -> int { return Graph->getArcCount(node); };
	auto nextOut = [this](int node, int curIndex) -> int { return acycNextEnabledOutArcIndex(Graph, SolverInstance, node, curIndex); };
	auto outArcByIdx = [this](int node, int curIndex) -> SATGraph::Arc* { return Graph->getArcs(node) + curIndex; };
	auto outwardVisit = [arcSourceNode](int node) -> bool { return node != arcSourceNode; };
	DFSwithDummyFollow<decltype(fstOut), decltype(lstOut),
										 decltype(nextOut), decltype(outArcByIdx),
										 decltype(outwardVisit)>(
		arcTargetNode, DFSTree, fstOut, lstOut, nextOut, outArcByIdx, outwardVisit);

	if (DFSTree.InnerTree.hasCurrentTag(arcSourceNode))
	{
		int clauselen = 0;

#ifdef ACYCDEBUG
		printf("Found a cycle.\n");
#endif
		/* Cycle found: recover path from n1 to n2 (backwards, and form clause. */

		// Initialize the clause.
		acyc_clause.clearunboxed();
		acyc_clause.push(~p);

#ifdef ACYCDEBUG
		printf("%i ",toInt(var(p)));
#endif

		clauselen += 1;
		while(arcSourceNode != arcTargetNode) {
			Lit arcLit = DFSTree.InnerTree.getParentArcLit(arcSourceNode);

#ifdef ACYCDEBUG
			printf("%i ", ConvertLiteralToInt(arcLit));
#endif

			clauselen += 1;
			acyc_clause.push(~arcLit); // Add negated arc variable to the clause

			arcSourceNode = DFSTree.InnerTree.getParent(arcSourceNode);
		}

		Propagator::Effect e = addNewClause(acyc_clause, false);

#ifdef ACYCDEBUG
		printf("Cycle clause ready (length %i). Cede control to analyze.\n",clauselen);
#endif

		// Clause complete. Return exit code for "conflict found", and
		// let the CDCL analyze procedure take over.
		return (e == CONFLICT);
	}

	if (SolverInstance->heavy_propagation == false)
		return false;

#ifdef ACYCDEBUG
	printf("Now checking backwards arcs toward %i.\n",n1);
#endif

	/* Start using a new int tag for marking nodes. */

	bool lazyPropCompleted = false;

	auto fstIn = [this](int node) -> int { return acycFirstPossibleInArcIndex(Graph, SolverInstance, node); };
	auto lstIn = [this](int node) -> int { return Graph->getInverseArcCount(node); };
	auto nextIn = [this](int node, int curIndex) -> int { return acycNextPossibleInArcIndex(Graph, SolverInstance, node, curIndex); };
	auto inArcByIdx = [this](int node, int curIndex) -> SATGraph::Arc* { return Graph->getInverseArcs(node) + curIndex; };
	auto followArc = [this, &lazyPropCompleted, arcSourceNode, arcTargetNode, p](int sourceNode, int targetNode, Minisat::Lit label) mutable -> bool
		{
			if (lazyPropCompleted)
				return false;
			if (SolverInstance->value(label) == l_True)
				return true;
			if (DFSTree.InnerTree.hasPreviousTag(targetNode))
			{
				/* Almost cycle found: recover forward path from arcTargetNode to targetNode plus
				 * backward path from arcSourceNode to sourceNode
				 */

				// Add clause representing the almost-cycle

#ifdef ACYCDEBUG
				printf("Inferring literal -%i from acyclicity.\n",toInt(v));
#endif

				// Initialize the clause.

				acyc_clause.clearunboxed();
				acyc_clause.push(~label);	// Literal for the arc to be blocked.
				acyc_clause.push(~p);		// Literal for the arc just added.

				/* Recover the forward part of the almost-cycle from arcTargetNode. */

				while(targetNode != arcTargetNode)
				{
					Lit arcLit = DFSTree.InnerTree.getParentArcLit(targetNode);
					acyc_clause.push(~arcLit); // Add negated arc variable to the clause
					targetNode = DFSTree.InnerTree.getParent(targetNode);
				}

				/* Recover the backward part of the almost-cycle to sourceNode. */

				while(sourceNode != arcSourceNode) {
					Lit arcLit = DFSTree.InnerTree.getParentArcLit(sourceNode);
					acyc_clause.push(~arcLit); // Add negated arc variable to the clause
					sourceNode = DFSTree.InnerTree.getParent(sourceNode);
				}

				Propagator::Effect e = addNewClause(acyc_clause, lazyPropCompleted);
				assert(e != CONFLICT);
				if ((e != NO_EFFECT) && (SolverInstance->lazy_propagation || (e == DESTRUCTIVE_PROPAGATION)))
					lazyPropCompleted = true;
			}

			return false;
		};

	DFSwithDummyVisit<decltype(fstIn), decltype(lstIn),
										decltype(nextIn), decltype(inArcByIdx),
										decltype(followArc)>(
		arcSourceNode, DFSTree, fstIn, lstIn, nextIn, inArcByIdx, followArc);

	return false;
}

const vec<Lit> &AcyclicityPropagator::explain()
{
	acyc_clause.clear();
	for (int i = 0; i < Graph->nodeCount; i++)
	{
		SATGraph::Arc *arcs = Graph->getArcs(i);
		for (int j = 0; j < Graph->getArcCount(i); j++)
			if (SolverInstance->modelValue(arcs[j].arcLit) == l_False)
				acyc_clause.push(~arcs[i].arcLit);
	}

	return acyc_clause;
}
