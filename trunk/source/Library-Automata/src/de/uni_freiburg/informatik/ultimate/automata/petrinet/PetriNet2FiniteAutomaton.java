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
package de.uni_freiburg.informatik.ultimate.automata.petrinet;

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
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Given a Petri net, this class constructs a finite automaton that recognizes the same language.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <S>
 *            symbols type
 * @param <C>
 *            place content type
 */
public final class PetriNet2FiniteAutomaton<S, C> extends UnaryNetOperation<S, C, IStateFactory<C>> {
	private final IPetriNet<S, C> mOperand;
	private final NestedWordAutomaton<S, C> mResult;

	/**
	 * List of markings for which
	 * <ul>
	 * <li>there has already been a state constructed
	 * <li>outgoing transitions of this state have not yet been constructed.
	 * </ul>
	 */
	private final List<Marking<S, C>> mWorklist = new LinkedList<>();
	/**
	 * Maps a marking to the automaton state that represents this marking.
	 */
	private final Map<Marking<S, C>, C> mMarking2State = new HashMap<>();
	private final IPetriNet2FiniteAutomatonStateFactory<C> mContentFactory;

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
			final IPetriNet2FiniteAutomatonStateFactory<C> factory, final IPetriNet<S, C> operand) {
		super(services);
		mOperand = operand;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mContentFactory = factory;
		final Set<S> alphabet = new HashSet<>(operand.getAlphabet());
		final VpAlphabet<S> vpAlphabet = new VpAlphabet<S>(alphabet, Collections.emptySet(), Collections.emptySet());
		mResult = new NestedWordAutomaton<>(mServices, vpAlphabet,
				operand.getStateFactory());
		getState(operand.getInitialMarking(), true);
		while (!mWorklist.isEmpty()) {
			final Marking<S, C> marking = mWorklist.remove(0);
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
	private C getState(final Marking<S, C> marking, final boolean isInitial) {
		C state = mMarking2State.get(marking);
		if (state == null) {
			final boolean isFinal = mOperand.isAccepting(marking);
			state = mContentFactory.getContentOnPetriNet2FiniteAutomaton(marking);
			mResult.addState(isInitial, isFinal, state);
			mMarking2State.put(marking, state);
			mWorklist.add(marking);
		}
		return state;
	}

	private Collection<C> getMarkingContents(final Set<Place<C>> marking) {
		final ArrayList<C> result = new ArrayList<>(marking.size());
		for (final Place<C> place : marking) {
			result.add(place.getContent());
		}
		return result;
	}

	/**
	 * Given a marking. Get the state that represents the marking. Add all possible outgoing automaton transitions to
	 * state. Construct (and enqueue to worklist) successor states if necessary.
	 */
	private void constructOutgoingTransitions(final Marking<S, C> marking) {
		final C state = getState(marking, false);
		final Set<ITransition<S, C>> outgoing = getOutgoingNetTransitions(marking);
		for (final ITransition<S, C> transition : outgoing) {
			if (marking.isTransitionEnabled(transition)) {
				final Marking<S, C> succMarking = marking.fireTransition(transition);
				final C succState = getState(succMarking, false);
				mResult.addInternalTransition(state, transition.getSymbol(), succState);
			}
		}
	}

	private Set<ITransition<S, C>> getOutgoingNetTransitions(final Marking<S, C> marking) {
		final Set<ITransition<S, C>> transitions = new HashSet<>();
		for (final Place<C> place : marking) {
			transitions.addAll(mOperand.getSuccessors(place));
		}
		return transitions;
	}

	@Override
	protected IPetriNet<S, C> getOperand() {
		return mOperand;
	}

	@Override
	public INestedWordAutomaton<S, C> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<C> stateFactory) throws AutomataLibraryException {
		return true;
	}
}
