/*
 * GeneralizedNonreachabilityPropagator.h
 * Copyright (C) 2015 Shahab <shahab.tasharrofi@aalto.fi>
 *
 * graph-minisat is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * graph-minisat is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef _GENERALIZEDNONREACHABILITYPROPAGATOR_H_
#define _GENERALIZEDNONREACHABILITYPROPAGATOR_H_

#include "Propagator.h"
#include "utils/GraphUtils.h"
#include "utils/FixedSizeIntSet.h"
#include "utils/FixedSizeIntMap.h"

using namespace std;

class GeneralizedNonreachabilityPropagator: public Propagator 
{
	private:
		SATGraph *Graph;
		vec<Lit> nonreachClause;
		bool initialized;

		FixedSizeIntMap<int> sourceNodeFromLit;
		FixedSizeIntMap<int> destNodeFromLit;

		vector<int> nodeToFRIndex;
		vector<int> nodeToBRIndex;
		unordered_map<int, unordered_map<int, Lit> > litFromNodePair;

		vector<OrderedDFSTree> forwardDFSTrees;
		vector<OrderedDFSTree> backwardDFSTrees;

		void initializeReachabilities();
		void extendReachabilities(int sourceNode, int targetNode, Lit arcLit);
	protected:
		// Overridden protected methods from Propagator class
		virtual bool propagate(Lit p) override;
		virtual void cancelUntil(int level) override;
	public:
		GeneralizedNonreachabilityPropagator(Solver *S, int nOfVars, SATGraph *G, const vector< tuple<int, int, Lit> > &NonreachablePairs);

		// Overridden public methods from Propagator class
		virtual bool initialize(void) override;
		virtual const vec<Lit> &explain() override;
		virtual bool isTheoryVar(Var v) override;

		virtual Propagator *copy(Solver *S);
};

#endif // _GENERALIZEDNONREACHABILITYPROPAGATOR_H_

