
#ifndef ACYCLICITY_PROPAGATOR_H
#define ACYCLICITY_PROPAGATOR_H

#include "Propagator.h"
#include "utils/SATGraph.h"
#include "utils/GraphUtils.h"

using namespace Minisat;

class AcyclicityPropagator : public Propagator
{
	private:
		SATGraph *Graph;
		OrderedDFSTree DFSTree;
		vec<Lit> acyc_clause;
	protected:
		// Overridden protected methods from Propagator class
		virtual bool propagate(Lit p) override;
	public:
		AcyclicityPropagator(Solver *S, SATGraph *G);

		// Overridden public methods from Propagator class
		virtual bool initialize(void) override;
		virtual const vec<Lit> &explain() override;
		virtual bool isTheoryVar(Var v) override;

		virtual Propagator *copy(Solver *S) { return new AcyclicityPropagator(S, Graph); }
};

#endif
