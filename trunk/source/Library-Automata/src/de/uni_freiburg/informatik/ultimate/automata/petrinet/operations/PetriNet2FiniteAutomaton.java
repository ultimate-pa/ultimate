/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Given a Petri net, this class constructs a finite automaton that recognizes the same language.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbols type
 * @param <PLACE>
 *            place content type
 */
public final class PetriNet2FiniteAutomaton<LETTER, PLACE> extends UnaryNetOperation<LETTER, PLACE, IStateFactory<PLACE>> {
	private final IPetriNet<LETTER, PLACE> mOperand;
	private final NestedWordAutomaton<LETTER, PLACE> mResult;

	/**
	 * List of markings for which
	 * <ul>
	 * <li>there has already been a state constructed
	 * <li>outgoing transitions of this state have not yet been constructed.
	 * </ul>
	 */
	private final List<Marking<LETTER, PLACE>> mWorklist = new LinkedList<>();
	/**
	 * Maps a marking to the automaton state that represents this marking.
	 */
	private final Map<Marking<LETTER, PLACE>, PLACE> mMarking2State = new HashMap<>();
	private final IPetriNet2FiniteAutomatonStateFactory<PLACE> mContentFactory;

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param factory
	 *            content factory
	 * @param operand
	 *            operand Petri net
	 */
	public PetriNet2FiniteAutomaton(final AutomataLibraryServices services,
			final IPetriNet2FiniteAutomatonStateFactory<PLACE> factory, final IPetriNet<LETTER, PLACE> operand) {
		super(services);
		mOperand = operand;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mContentFactory = factory;
		final Set<LETTER> alphabet = new HashSet<>(operand.getAlphabet());
		final VpAlphabet<LETTER> vpAlphabet = new VpAlphabet<LETTER>(alphabet, Collections.emptySet(), Collections.emptySet());
		mResult = new NestedWordAutomaton<>(mServices, vpAlphabet, factory);
		getState(new Marking(operand.getInitialPlaces()), true);
		while (!mWorklist.isEmpty()) {
			final Marking<LETTER, PLACE> marking = mWorklist.remove(0);
			constructOutgoingTransitions(marking);
		}

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mResult.sizeInformation();
	}

	/**
	 * Returns the automaton state that represents marking. If this state is not yet constructed, construct it and
	 * enqueue the marking. If it has to be constructed it is an initial state iff isInitial is true.
	 */
	private PLACE getState(final Marking<LETTER, PLACE> marking, final boolean isInitial) {
		PLACE state = mMarking2State.get(marking);
		if (state == null) {
			final boolean isFinal = mOperand.isAccepting(marking);
			state = mContentFactory.getContentOnPetriNet2FiniteAutomaton(marking);
			mResult.addState(isInitial, isFinal, state);
			mMarking2State.put(marking, state);
			mWorklist.add(marking);
		}
		return state;
	}

	private Collection<PLACE> getMarkingContents(final Set<PLACE> marking) {
		final ArrayList<PLACE> result = new ArrayList<>(marking.size());
		for (final PLACE place : marking) {
			result.add(place);
		}
		return result;
	}

	/**
	 * Given a marking. Get the state that represents the marking. Add all possible outgoing automaton transitions to
	 * state. Construct (and enqueue to worklist) successor states if necessary.
	 */
	private void constructOutgoingTransitions(final Marking<LETTER, PLACE> marking) {
		final PLACE state = getState(marking, false);
		final Set<ITransition<LETTER, PLACE>> outgoing = getOutgoingNetTransitions(marking);
		for (final ITransition<LETTER, PLACE> transition : outgoing) {
			if (marking.isTransitionEnabled(transition, mOperand)) {
				final Marking<LETTER, PLACE> succMarking = marking.fireTransition(transition, mOperand);
				final PLACE succState = getState(succMarking, false);
				mResult.addInternalTransition(state, transition.getSymbol(), succState);
			}
		}
	}

	private Set<ITransition<LETTER, PLACE>> getOutgoingNetTransitions(final Marking<LETTER, PLACE> marking) {
		final Set<ITransition<LETTER, PLACE>> transitions = new HashSet<>();
		for (final PLACE place : marking) {
			transitions.addAll(mOperand.getSuccessors(place));
		}
		return transitions;
	}

	@Override
	protected IPetriNet<LETTER, PLACE> getOperand() {
		return mOperand;
	}

	@Override
	public INestedWordAutomaton<LETTER, PLACE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<PLACE> stateFactory) throws AutomataLibraryException {
		return true;
	}
}
