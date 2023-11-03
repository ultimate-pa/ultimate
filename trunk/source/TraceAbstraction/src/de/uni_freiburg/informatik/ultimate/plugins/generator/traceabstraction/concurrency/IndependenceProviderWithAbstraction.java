/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceBuilder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.IRefinableAbstraction;

/**
 * An {@link IRefinableIndependenceProvider} implementation for the case where we consider abstract commutativity given
 * by some refinable abstraction function.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <H>
 *            The type of abstraction levels
 */
class IndependenceProviderWithAbstraction<L extends IIcfgTransition<?>, H>
		implements IRefinableIndependenceProvider<L> {
	private final IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, H, L> mRefinableAbstraction;
	private final IIndependenceRelation<IPredicate, L> mUnderlyingIndependence;
	private H mAbstractionLevel;

	public IndependenceProviderWithAbstraction(
			final IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, H, L> abstraction,
			final IIndependenceRelation<IPredicate, L> underlyingIndependence) {
		mRefinableAbstraction = abstraction;
		mUnderlyingIndependence = underlyingIndependence;
	}

	@Override
	public void initialize() {
		mAbstractionLevel = mRefinableAbstraction.getInitial();
	}

	@Override
	public void refine(final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinement) {
		final H newLevel = mRefinableAbstraction.refine(mAbstractionLevel, refinement);
		assert mRefinableAbstraction.getHierarchy().compare(newLevel, mAbstractionLevel)
				.isLessOrEqual() : "Refinement must yield a lower abstraction level";
		mAbstractionLevel = newLevel;
	}

	@Override
	public IIndependenceRelation<IPredicate, L> retrieveIndependence() {
		return IndependenceBuilder.fromPredicateActionIndependence(mUnderlyingIndependence)
				// Apply abstraction to each letter before checking commutativity.
				.withAbstraction(mRefinableAbstraction, mAbstractionLevel)
				// Retrieve the constructed relation.
				.build();
	}
}
