/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotation.ISRLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * On-the-fly construction of an IDP-DFA for the underlying finite automaton constructed from a product CFG. Computes
 * the transition function for interrupt-driven programs such that in the case that an interrupt is active, only the
 * successor transitions of this specific interrupt are returned.
 *
 * @param <S>
 *            The type of states of the underlying automaton
 * @param <L>
 *            The type of transitions of the underlying automaton
 */
public class FiniteAutomaton2IDPAutomaton<L extends IIcfgTransition<?>, S extends IPredicate>
		implements INwaOutgoingLetterAndTransitionProvider<L, S> {

	private final INwaOutgoingLetterAndTransitionProvider<L, S> mFiniteAutomaton;
	private final Function<S, IcfgLocation[]> mState2LocationsFunction;
	private final Map<IElement, InterruptAnnotation> mInterruptAnnotations = new HashMap<>();

	/**
	 * Construct an IDP-DFA
	 *
	 * @param operand
	 *            Underlying automaton representing the program
	 * @param state2Locations
	 *            Function that maps states of the operand to Icfg locations of the original program
	 */
	public FiniteAutomaton2IDPAutomaton(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final Function<S, IcfgLocation[]> state2Locations) {
		mFiniteAutomaton = operand;
		mState2LocationsFunction = state2Locations;
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state, final L letter) {
		final var petriSuccessors = mFiniteAutomaton.internalSuccessors(state, letter);
		// Filter out transitions that are not part of the ISR
		return () -> StreamSupport.stream(petriSuccessors.spliterator(), false).filter(t -> isIdpTransition(t, state))
				.iterator();
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state) {
		final var petriSuccessors = mFiniteAutomaton.internalSuccessors(state);
		// Filter out transitions that are not part of the ISR
		return () -> StreamSupport.stream(petriSuccessors.spliterator(), false).filter(t -> isIdpTransition(t, state))
				.iterator();
	}

	/**
	 * Check whether the transition of the underlying automaton is also a successor of the state for the IDP transition
	 * function.
	 *
	 * @param transition
	 *            Outgoing transition of the state
	 * @param state
	 *            The corresponding state
	 * @return True if the transition is also part of the IDP, false otherwise
	 */
	private boolean isIdpTransition(final OutgoingInternalTransition<L, S> transition, final S state) {
		final var stateIcfgLocations = List.of(mState2LocationsFunction.apply(state));
		final var isrLocations = new ArrayList<IcfgLocation>(stateIcfgLocations.size());
		for (final IcfgLocation icfgLocation : stateIcfgLocations) {
			final var annotation = getInterruptAnnotation(icfgLocation);
			if (annotation == null) {
				continue;
			}
			if (annotation.getIsrLocation() == ISRLocation.ENTRY) {
				// If the successor is an entry edge, the ISR is not active yet
				continue;
			}
			isrLocations.add(icfgLocation);
		}
		// If no ISR is active, no transition gets filtered out
		if (isrLocations.isEmpty()) {
			return true;
		}
		final var singleIsrLocation = DataStructureUtils.getOneAndOnly(isrLocations, "active isr");

		// If one (and only one) ISR is active, the transition has to be part of this ISR, i.e. has to be a successor of
		// the active ISR-location in the CFG
		return transition.getLetter().getSource() == singleIsrLocation;
	}

	private InterruptAnnotation getInterruptAnnotation(final IElement element) {
		return mInterruptAnnotations.computeIfAbsent(element, e -> InterruptAnnotation.getAnnotation(e));
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		return mFiniteAutomaton.getVpAlphabet();
	}

	@Override
	public S getEmptyStackState() {
		return mFiniteAutomaton.getEmptyStackState();
	}

	@Override
	public Iterable<S> getInitialStates() {
		return mFiniteAutomaton.getInitialStates();
	}

	@Override
	public boolean isInitial(final S state) {
		return mFiniteAutomaton.isInitial(state);
	}

	@Override
	public boolean isFinal(final S state) {
		return mFiniteAutomaton.isFinal(state);
	}

	@Override
	public int size() {
		return mFiniteAutomaton.size();
	}

	@Override
	public String sizeInformation() {
		return mFiniteAutomaton.sizeInformation();
	}

	@Override
	public Iterable<OutgoingCallTransition<L, S>> callSuccessors(final S state, final L letter) {
		return Collections.emptySet();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, S>> returnSuccessors(final S state, final S hier, final L letter) {
		return Collections.emptySet();
	}
}
