
#ifndef REACHABILITY_PROPAGATOR_H
#define REACHABILITY_PROPAGATOR_H

#include <vector>
#include <unordered_set>

#include "utils/GraphUtils.h"
#include "Propagator.h"
#include "utils/FixedSizeIntSet.h"

#define PROPAGATEBRIDGES

using namespace Minisat;
using namespace std;

class ReachabilityPropagator : public Propagator
{
	private:
		int Source;
		FixedSizeIntSet<VoidTrait> DestinationsSet;
		vector<int> DestinationsList;
		SATGraph *Graph;
		vec<Lit> reach_clause;

		bool Initialized;
		TarjanTree Tree;
		FixedSizeIntSet<VoidTrait> TreeEdgeLits;
#ifdef COMPUTE_NON_BRIDGE_WITNESSES
		FixedSizeIntSet<VoidTrait> BridgeWatchedArcLits;
#endif
		// initializeWatchTree:
		//   returns true if initialization was successful
		//
		//   if not successful, reach_clause is filled with a description of the cut
		//     that separates the start node from some end node
		bool initializeWatchTree();

#ifdef PROPAGATEBRIDGES
		void findAndPropagateBridges();
#endif
		bool performPropagations(bool checkNonreachability);
	public:
		ReachabilityPropagator(Solver *S, int nOfVars, SATGraph *G, int SourceNode, const unordered_set<int> &DestNodes);

		virtual bool initialize(void) override;
		virtual bool propagate(Lit p) override;
		virtual bool propagate(int start, int end) override;
		virtual const vec<Lit> &explain() override;
		virtual void cancelUntil(int level) override;
		virtual bool isTheoryVar(Var v) override;

		virtual Propagator *copy(Solver *S) override;
};

#endif
