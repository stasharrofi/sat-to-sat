/* -*- Mode: C; indent-tabs-mode: t; c-basic-offset: 2; tab-width: 2 -*-  */
/*
 * GeneralizedReachabilityPropagator.h
 * Copyright (C) 2015 Shahab Tasharrofi <>
 *
 * minisatAcycReach is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * minisatAcycReach is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef _GENERALIZEDREACHABILITYPROPAGATOR_H_
#define _GENERALIZEDREACHABILITYPROPAGATOR_H_

#include "Propagator.h"
#include "utils/GraphUtils.h"
#include "utils/FixedSizeIntSet.h"
#include "utils/FixedSizeIntMap.h"
#include <unordered_map>

using namespace Minisat;
using namespace std;

class GeneralizedReachabilityPropagator: public Propagator 
{
	private:
		int Source;
		FixedSizeIntMap<Lit> DestinationsMap;
		vector<int> DestinationNodes;
		FixedSizeIntSet<VoidTrait> DestinationLits;
		SATGraph *Graph;
		vec<Lit> reach_clause;

		TarjanTree Tree;

		bool Initialized;
		FixedSizeIntSet<VoidTrait> TreeEdgeLits;
		FixedSizeIntSet<VoidTrait> BridgeWatchedArcLits;

		bool performPropagations(bool findNewDFSTree, bool checkNonreachability);
	protected:
		// Overridden protected methods from Propagator class
		virtual bool propagate(int start, int end) override;
		virtual bool propagate(Lit p) override;
		virtual void cancelUntil(int level) override;
	public:
		GeneralizedReachabilityPropagator(Solver *S, int nOfVars, SATGraph *G, int SourceNode, const unordered_map<int, Lit> &DestNodes);

		// Overridden public methods from Propagator class
		virtual bool initialize(void) override;
		virtual const vec<Lit> &explain() override;
		virtual bool isTheoryVar(Var v) override;

		virtual Propagator *copy(Solver *S);
};

#endif // _GENERALIZEDREACHABILITYPROPAGATOR_H_

