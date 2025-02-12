/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.AutomatonTransition.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Converts an {@link INwaOutgoingLetterAndTransitionProvider} to an Ultimate model.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class NwaToUltimateModel<LETTER, STATE> {
	private static final String CREATING_NODE = "Creating Node: ";

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	private final INestedWordAutomaton<LETTER, STATE> mNWA;

	private final Map<STATE, AutomatonState> mConstructedStates = new HashMap<>();
	private final Deque<STATE> mQueue = new ArrayDeque<>();

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param nwaSimple
	 *            The nested word automaton that shall be transformed.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if timeout is reached while collecting reachable states of the automaton
	 */
	public NwaToUltimateModel(final AutomataLibraryServices services,
			final INwaOutgoingTransitionProvider<LETTER, STATE> nwaSimple) throws AutomataOperationCanceledException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);

		if (nwaSimple instanceof INestedWordAutomaton) {
			mNWA = (INestedWordAutomaton<LETTER, STATE>) nwaSimple;
		} else {
			mNWA = new NestedWordAutomatonReachableStates<>(mServices, nwaSimple);
		}
	}

	/**
	 * @return Ultimate model
	 */
	public IElement transformToUltimateModel() {
		mConstructedStates.clear();
		mQueue.clear();

		final AutomatonState graphroot = new AutomatonState("Sucessors of this node are the initial states", false);

		// add all initial states to model - all are successors of the graphroot
		for (final STATE state : mNWA.getInitialStates()) {
			final AutomatonState vsn = getOrConstructState(state);
			new AutomatonTransition(graphroot, Transition.INITIAL, "", null, vsn);
		}

		while (!mQueue.isEmpty()) {
			final STATE state = mQueue.removeFirst();
			final AutomatonState vsn = mConstructedStates.get(state);

			// internal transitions
			addTransitions(vsn, Transition.INTERNAL, null, mNWA.internalSuccessors(state));

			// call transitions
			addTransitions(vsn, Transition.CALL, null, mNWA.callSuccessors(state));

			// return transitions
			for (final STATE hierPredState : mNWA.getStates()) {
				addTransitions(vsn, Transition.RETURN, hierPredState.toString(),
						mNWA.returnSuccessorsGivenHier(state, hierPredState));
			}
		}
		return graphroot;
	}

	protected final AutomatonState getOrConstructState(final STATE state) {
		return mConstructedStates.computeIfAbsent(state, this::createStateInternal);
	}

	private AutomatonState createStateInternal(final STATE state) {
		final var vsn = createState(state);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(CREATING_NODE + vsn.toString());
		}
		mQueue.addLast(state);
		return vsn;
	}

	protected AutomatonState createState(final STATE state) {
		return new AutomatonState(state, mNWA.isFinal(state));
	}

	protected void addTransitions(final AutomatonState vsn, final Transition transitionType, final String hierPred,
			final Iterable<? extends IOutgoingTransitionlet<LETTER, STATE>> transitions) {
		for (final IOutgoingTransitionlet<LETTER, STATE> trans : transitions) {
			final LETTER symbol = trans.getLetter();
			final STATE succState = trans.getSucc();
			final AutomatonState succVsn = getOrConstructState(succState);
			new AutomatonTransition(vsn, transitionType, symbol, hierPred, succVsn);
		}
	}
}
