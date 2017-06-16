
#ifndef SAT_GRAPH_H
#define SAT_GRAPH_H

#include <vector>

/*________________________________________________________________________
|
| SATgraph
|
| Description:
|   Representation of directed graphs, with support for operations needed
|   in propagating acyclicity constraints.
|
|___________________________________________________________________________*/

class OrderedDFSTree;

class SATGraph {

public:
  struct Arc { Minisat::Lit arcLit; int succNode; };
  struct NodeData { Arc *arcList; int arcCount; };

  int nodeCount;

private:
  NodeData *arcs;		// Outgoing arcs
  NodeData *inverseArcs;	// Incoming arcs

	int *arcSources;	// s for arc p:s->t
  int *arcTargets;	// t for arc p:s->t
	Minisat::Lit *arcLabels; // p for arc p:s->t

  int minArcIndex, maxArcIndex;

	bool **forwardReachability;
	bool **backwardReachability;
	OrderedDFSTree *dfsTree;

	void computeForwardReachability(int node);
	void computeBackwardReachability(int node);
public:

  void createGraph(int nOfVars);
  void initGraph(int nOfNodes);
  void createInverseArcs();
  void createNode(int node, int nOfArcs);
  void addArc(Minisat::Lit p,int node,int succNode);

  int getArcCount(int node) { return arcs[node].arcCount; }
  Arc *getArcs(int node) { return arcs[node].arcList; }

  int getInverseArcCount(int node) { return inverseArcs[node].arcCount; }
  Arc *getInverseArcs(int node) { return inverseArcs[node].arcList; }

  bool isGraphArc(Minisat::Var v)
	{
		int i = Minisat::toInt(v);
		return ((i >= minArcIndex) && (i <= maxArcIndex)) && (arcSources[i] >= 0);
	}
	bool isGraphArc(Minisat::Lit p) { return isGraphArc(var(p)); }

  int sourceNode(Minisat::Lit p) { return arcSources[var(p)]; }
  int targetNode(Minisat::Lit p) { return arcTargets[var(p)]; }
  Minisat::Lit label(Minisat::Lit p) { return arcLabels[var(p)]; }

	/* isForwardReachable(source, target):
	 *   returns true if target is reachable from source in the graph
	 */
	bool isForwardReachable(int source, int target)
	{
		if ((forwardReachability == NULL) || (forwardReachability[source] == NULL))
			computeForwardReachability(source);
		return forwardReachability[source][target];
	}

	/* isBackwardReachable(source, target):
	 *   returns true if, in the inverse graph, target is reachable from source
	 */
	bool isBackwardReachable(int source, int target)
	{
		if ((backwardReachability == NULL) || (backwardReachability[source] == NULL))
			computeBackwardReachability(source);
		return backwardReachability[source][target];
	}
};

#endif
