/*
 * Copyright (C) 2021 Dennis Wölfing
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Performs a Lipton Reduction on a Petri net taking into account predicates added by previous Trace Abstrction steps.
 *
 * @author Dennis Wölfing
 *
 * @param <L>
 *            The type of letters labeling the net's transitions.
 */
public class LiptonReductionWithPredicates<L> extends LiptonReduction<L, IPredicate> {
	private final BasicPredicateFactory mPredicateFactory;

	/**
	 * Performs Lipton reduction on the given Petri net.
	 *
	 * @param services
	 *            A {@link AutomataLibraryServices} instance.
	 * @param petriNet
	 *            The Petri Net on which the Lipton reduction should be performed.
	 * @param compositionFactory
	 *            An {@link ICompositionFactory} capable of performing compositions for the given alphabet.
	 * @param independenceRelation
	 *            The independence relation used for mover checks.
	 * @param predicateFactory
	 *            A predicate factory for predicates of the control flow graph.
	 */
	public LiptonReductionWithPredicates(final IUltimateServiceProvider services,
			final BoundedPetriNet<L, IPredicate> petriNet, final ICompositionFactory<L> compositionFactory,
			final IIndependenceRelation<IPredicate, L> independenceRelation,
			final BasicPredicateFactory predicateFactory) {
		super(new AutomataLibraryServices(services), petriNet, compositionFactory, independenceRelation);
		mPredicateFactory = predicateFactory;
	}

	@Override
	protected boolean isLeftMover(final BoundedPetriNet<L, IPredicate> petriNet, final ITransition<L, IPredicate> t1,
			final Set<L> coEnabledTransitions) {
		mStatistics.reportMoverChecks(coEnabledTransitions.size());
		// TODO: The mover check currently only accepts a predicate for the first transition.
		return coEnabledTransitions.stream().allMatch(t3 -> mMoverCheck.contains(null, t3, t1.getSymbol()));
	}

	@Override
	protected boolean isRightMover(final BoundedPetriNet<L, IPredicate> petriNet, final ITransition<L, IPredicate> t1,
			final Set<L> coEnabledTransitions) {
		mStatistics.reportMoverChecks(coEnabledTransitions.size());
		final Set<IPredicate> preconditions = petriNet.getPredecessors(t1);
		final IPredicate predicate = mPredicateFactory.and(preconditions);

		return coEnabledTransitions.stream().allMatch(t3 -> mMoverCheck.contains(predicate, t1.getSymbol(), t3));
	}
}
