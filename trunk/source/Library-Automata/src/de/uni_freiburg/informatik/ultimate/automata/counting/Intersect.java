/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.counting;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Intersection method for Counting Automata
 *
 * @author Marcel Ebbinghaus
 * @author who is the author?
 */
public class Intersect<LETTER, STATE, CRSF extends IStateFactory<STATE>> implements IOperation<LETTER, STATE, CRSF> {

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	private final CountingAutomaton<LETTER, STATE> mFstOperand;
	private final CountingAutomaton<LETTER, STATE> mSndOperand;
	private final CountingAutomaton<LETTER, STATE> mResult;
	private final IIntersectionStateFactory<STATE> mStateFactory;

	public Intersect(final AutomataLibraryServices services, final IIntersectionStateFactory<STATE> stateFactory,
			final CountingAutomaton<LETTER, STATE> fstOperand, final CountingAutomaton<LETTER, STATE> sndOperand)
			throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(this.getClass());
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		mStateFactory = stateFactory;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mResult = computeResult();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	private CountingAutomaton<LETTER, STATE> computeResult() {
		final Set<LETTER> intersectAlphabet = mFstOperand.getAlphabet();
		final ArrayList<Counter> intersectCounter = new ArrayList<>();
		for (final Counter counter : mFstOperand.getCounter()) {
			intersectCounter.add(counter.copyCounter());
		}
		for (final Counter counter : mSndOperand.getCounter()) {
			intersectCounter.add(counter.copyCounter());
		}
		final Set<STATE> intersectStates = new HashSet<>();
		final Map<STATE, InitialCondition> intersectInitialConditions = new HashMap<>();
		final Map<STATE, FinalCondition> intersectFinalConditions = new HashMap<>();
		final Map<STATE, ArrayList<Transition<LETTER, STATE>>> intersectTransitions = new HashMap<>();

		final Map<ArrayList<STATE>, STATE> stateMemory = new HashMap<>();

		// states
		for (final STATE stateFstOp : mFstOperand.getStates()) {

			for (final STATE stateSndOp : mSndOperand.getStates()) {

				final STATE newState = mStateFactory.intersection(stateFstOp, stateSndOp);
				intersectStates.add(newState);
				final ArrayList<STATE> statePair = new ArrayList<>();
				statePair.add(stateFstOp);
				statePair.add(stateSndOp);
				stateMemory.put(statePair, newState);
			}
		}

		for (final STATE stateFstOp : mFstOperand.getStates()) {

			for (final STATE stateSndOp : mSndOperand.getStates()) {

				final ArrayList<STATE> statePair = new ArrayList<>();
				statePair.add(stateFstOp);
				statePair.add(stateSndOp);
				final STATE newState = stateMemory.get(statePair);

				// initialConditions
				final ConjunctGuards initialConjunction = new ConjunctGuards(
						mFstOperand.getInitialConditions().get(stateFstOp).copyInitialCondition().getCondition(),
						mSndOperand.getInitialConditions().get(stateSndOp).copyInitialCondition().getCondition());
				final ArrayList<ArrayList<Guard>> newInitialConditions = initialConjunction.getResult();
				intersectInitialConditions.put(newState, new InitialCondition(newInitialConditions));

				// finalConditions
				final ConjunctGuards finalConjunction = new ConjunctGuards(
						mFstOperand.getFinalConditions().get(stateFstOp).copyFinalCondition().getCondition(),
						mSndOperand.getFinalConditions().get(stateSndOp).copyFinalCondition().getCondition());
				final ArrayList<ArrayList<Guard>> newFinalConditions = finalConjunction.getResult();
				intersectFinalConditions.put(newState, new FinalCondition(newFinalConditions));

				// transitions
				final ArrayList<Transition<LETTER, STATE>> newOutgoingTransitions = new ArrayList<>();

				for (final Transition<LETTER, STATE> transOfStateFstOp : mFstOperand.getTransitions().get(stateFstOp)) {

					for (final Transition<LETTER, STATE> transOfStateSndOp : mSndOperand.getTransitions()
							.get(stateSndOp)) {

						if (transOfStateFstOp.getLetter().equals(transOfStateSndOp.getLetter())) {

							final Transition<LETTER, STATE> transCopy1 = transOfStateFstOp.copyTransition();
							final Transition<LETTER, STATE> transCopy2 = transOfStateSndOp.copyTransition();
							final ConjunctGuards transitionConjunction =
									new ConjunctGuards(transCopy1.getGuards(), transCopy2.getGuards());
							final ArrayList<ArrayList<Guard>> newTransitionGuards = transitionConjunction.getResult();
							final ArrayList<Update> newTransitionUpdates = new ArrayList<>(transCopy1.getUpdates());
							newTransitionUpdates.addAll(transCopy2.getUpdates());
							final ArrayList<STATE> sucStatePair = new ArrayList<>();
							sucStatePair.add(transCopy1.getSucState());
							sucStatePair.add(transCopy2.getSucState());
							final STATE newSuccessorState = stateMemory.get(sucStatePair);
							newOutgoingTransitions.add(new Transition<>(transCopy1.getLetter(), newState,
									newSuccessorState, newTransitionGuards, newTransitionUpdates));
						}
					}
				}
				intersectTransitions.put(newState, newOutgoingTransitions);
			}
		}

		// result
		final CountingAutomaton<LETTER, STATE> resultAutomaton =
				new CountingAutomaton<>(mServices, intersectAlphabet, intersectStates, intersectCounter,
						intersectInitialConditions, intersectFinalConditions, intersectTransitions);
		return resultAutomaton;
	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName() + ". First operand " + getFirstOperand().sizeInformation()
				+ " Second operand " + getSecondOperand().sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mResult.sizeInformation();
	}

	public CountingAutomaton<LETTER, STATE> getFirstOperand() {
		return mFstOperand;
	}

	public CountingAutomaton<LETTER, STATE> getSecondOperand() {
		return mSndOperand;
	}

	@Override
	public CountingAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataLibraryException {
		// TODO #CountingAutomataTodo: how can we check that the result is correct
		return true;
	}

}
