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
 * Concatenation method for Counting Automata
 *
 * @author Marcel Ebbinghaus
 * @author who is the author?
 */
public class Concatenation<LETTER, STATE, CRSF extends IStateFactory<STATE>>
		implements IOperation<LETTER, STATE, CRSF> {

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	private final CountingAutomaton<LETTER, STATE> mFstOperand;
	private final CountingAutomaton<LETTER, STATE> mSndOperand;
	private final CountingAutomaton<LETTER, STATE> mResult;
	private final IIntersectionStateFactory<STATE> mStateFactory;

	public Concatenation(final AutomataLibraryServices services, final IIntersectionStateFactory<STATE> stateFactory,
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
		final Set<LETTER> concatenationAlphabet = new HashSet<>(mFstOperand.getAlphabet());
		final ArrayList<Counter> concatenationCounter = new ArrayList<>();
		for (final Counter counter : mFstOperand.getCounter()) {
			concatenationCounter.add(counter.copyCounter());
		}
		for (final Counter counter : mSndOperand.getCounter()) {
			concatenationCounter.add(counter.copyCounter());
		}
		final Set<STATE> concatenationStates = new HashSet<>(mFstOperand.getStates());
		concatenationStates.addAll(mSndOperand.getStates());
		final Map<STATE, InitialCondition> concatenationInitialConditions = new HashMap<>();
		final Map<STATE, FinalCondition> concatenationFinalConditions = new HashMap<>();
		final Map<STATE, ArrayList<Transition<LETTER, STATE>>> concatenationTransitions = new HashMap<>();

		// initialize parameters of fstOperand
		for (final STATE state : mFstOperand.getStates()) {
			concatenationInitialConditions.put(state,
					mFstOperand.getInitialConditions().get(state).copyInitialCondition());
			concatenationFinalConditions.put(state, mFstOperand.getFinalConditions().get(state).copyFinalCondition());
			final ArrayList<Transition<LETTER, STATE>> transitionList = new ArrayList<>();
			for (final Transition<LETTER, STATE> transition : mFstOperand.getTransitions().get(state)) {
				transitionList.add(transition.copyTransition());
			}
			concatenationTransitions.put(state, transitionList);
		}

		// initialize parameters of SndOperand
		for (final STATE state : mSndOperand.getStates()) {
			final Guard newGuardFalse = new Guard();
			newGuardFalse.changeTermType(TermType.FALSE);
			final ArrayList<Guard> guardListFalse = new ArrayList<>();
			guardListFalse.add(newGuardFalse);
			final ArrayList<ArrayList<Guard>> newInitialConditionList = new ArrayList<>();
			newInitialConditionList.add(guardListFalse);
			final InitialCondition newInitialCondition = new InitialCondition(newInitialConditionList);
			concatenationInitialConditions.put(state, newInitialCondition);
			concatenationFinalConditions.put(state, mSndOperand.getFinalConditions().get(state).copyFinalCondition());
			final ArrayList<Transition<LETTER, STATE>> transitionList = new ArrayList<>();
			for (final Transition<LETTER, STATE> transition : mSndOperand.getTransitions().get(state)) {
				transitionList.add(transition.copyTransition());
			}
			concatenationTransitions.put(state, transitionList);
		}

		// connect finalStates of mFstOperand with initialStates of mSndOperand
		for (final STATE stateFstOp : mFstOperand.getStates()) {

			if (mFstOperand.getFinalConditions().get(stateFstOp).getCondition().get(0).get(0)
					.getTermType() != TermType.FALSE) {

				final ArrayList<Transition<LETTER, STATE>> newTransitions =
						new ArrayList<>(concatenationTransitions.get(stateFstOp));
				final ArrayList<ArrayList<Guard>> newFinalConditionsList = new ArrayList<>();

				for (final STATE stateSndOp : mSndOperand.getStates()) {

					if (mSndOperand.getInitialConditions().get(stateSndOp).getCondition().get(0).get(0)
							.getTermType() != TermType.FALSE) {

						// add new transitions
						for (final Transition<LETTER, STATE> transition : mSndOperand.getTransitions()
								.get(stateSndOp)) {

							final Transition<LETTER, STATE> transitionCopy = transition.copyTransition();
							final ConjunctGuards conjunction1 =
									new ConjunctGuards(transitionCopy.getGuards(), mFstOperand.getFinalConditions()
											.get(stateFstOp).copyFinalCondition().getCondition());
							final ConjunctGuards conjunction2 = new ConjunctGuards(conjunction1.getResult(), mSndOperand
									.getInitialConditions().get(stateSndOp).copyInitialCondition().getCondition());
							final Transition<LETTER, STATE> newTransition = new Transition<>(transitionCopy.getLetter(),
									stateFstOp, transitionCopy.getSucState(), conjunction2.getResult(),
									transitionCopy.getUpdates());
							newTransitions.add(newTransition);
						}

						// add finalCondition if stateSndOp is final as well
						if (mSndOperand.getFinalConditions().get(stateSndOp).getCondition().get(0).get(0)
								.getTermType() != TermType.FALSE) {

							final ConjunctGuards conjunction1 = new ConjunctGuards(
									mFstOperand.getFinalConditions().get(stateFstOp).copyFinalCondition()
											.getCondition(),
									mSndOperand.getInitialConditions().get(stateSndOp).copyInitialCondition()
											.getCondition());
							final ConjunctGuards conjunction2 = new ConjunctGuards(conjunction1.getResult(), mSndOperand
									.getFinalConditions().get(stateSndOp).copyFinalCondition().getCondition());

							newFinalConditionsList.addAll(conjunction2.getResult());
						}
					}
				}
				concatenationTransitions.put(stateFstOp, newTransitions);

				// construct finalCondition == false, if there were no states in mSndOperand which are initial and final
				// at once
				if (newFinalConditionsList.size() == 0) {

					final Guard newGuardFalse = new Guard();
					newGuardFalse.changeTermType(TermType.FALSE);
					final ArrayList<Guard> guardListFalse = new ArrayList<>();
					guardListFalse.add(newGuardFalse);
					newFinalConditionsList.add(guardListFalse);
				}
				final FinalCondition newFinalCondition = new FinalCondition(newFinalConditionsList);
				concatenationFinalConditions.put(stateFstOp, newFinalCondition);
			}
		}

		// result
		final CountingAutomaton<LETTER, STATE> resultAutomaton =
				new CountingAutomaton<>(mServices, concatenationAlphabet, concatenationStates, concatenationCounter,
						concatenationInitialConditions, concatenationFinalConditions, concatenationTransitions);
		return resultAutomaton;
	}

	@Override
	public CountingAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataLibraryException {
		// TODO: Check the result
		return true;
	}
}
