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
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Union method for Counting Automata
 *
 * @author Marcel Ebbinghaus
 * @author who is the author?
 */

public class Union<LETTER, STATE, CRSF extends IStateFactory<STATE>> implements IOperation<LETTER, STATE, CRSF> {

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	private final CountingAutomaton<LETTER, STATE> mFstOperand;
	private final CountingAutomaton<LETTER, STATE> mSndOperand;
	private final STATE mNewInitialState;
	private final CountingAutomaton<LETTER, STATE> mResult;
	private final ICaUnionStateFactory<STATE> mStateFactory;


	public Union(
			final AutomataLibraryServices services,
			final ICaUnionStateFactory<STATE> stateFactory,
			final CountingAutomaton<LETTER, STATE> fstOperand,
			final CountingAutomaton<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(this.getClass());
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		mStateFactory = stateFactory;
		mNewInitialState = mStateFactory.constructInitialState();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mResult = computeResult();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	private CountingAutomaton<LETTER, STATE> computeResult() {

		final Set<LETTER> unionAlphabet = mFstOperand.getAlphabet();
		final ArrayList<Counter> unionCounter = new ArrayList<Counter>();
		for (final Counter counter : mFstOperand.getCounter()) {
			unionCounter.add(counter.copyCounter());
		}
		for (final Counter counter : mSndOperand.getCounter()) {
			unionCounter.add(counter.copyCounter());
		}
		final Set<STATE> unionStates = new HashSet<STATE>();
		unionStates.addAll(mFstOperand.getStates());
		unionStates.addAll(mSndOperand.getStates());
		unionStates.add(mNewInitialState);
		final Map<STATE, InitialCondition> unionInitialConditions = new HashMap<STATE, InitialCondition>();
		final Map<STATE, FinalCondition> unionFinalConditions = new HashMap<STATE, FinalCondition>();
		final Map<STATE, ArrayList<Transition<LETTER, STATE>>> unionTransitions = new HashMap<STATE, ArrayList<Transition<LETTER, STATE>>>();

		//initialConditions
		final Guard newInitialGuard = new Guard();
		newInitialGuard.changeTermType(TermType.TRUE);
		final ArrayList<Guard> newGuardList = new ArrayList<Guard>();
		newGuardList.add(newInitialGuard);
		final ArrayList<ArrayList<Guard>> newInitialConditionList = new ArrayList<ArrayList<Guard>>();
		newInitialConditionList.add(newGuardList);
		unionInitialConditions.put(mNewInitialState, new InitialCondition(newInitialConditionList));
		addNewUnionInitialConditions(mFstOperand, unionInitialConditions);
		addNewUnionInitialConditions(mSndOperand, unionInitialConditions);

		//finalConditions
		final ArrayList<ArrayList<Guard>> newFinalConditionList = new ArrayList<ArrayList<Guard>>();
		addNewUnionFinalConditions(mFstOperand, newFinalConditionList, unionFinalConditions);
		addNewUnionFinalConditions(mSndOperand, newFinalConditionList, unionFinalConditions);

		//construct finalCondition == false, if there were no states in mFstOperand and mSndOperand which are initial and final at once
		if (newFinalConditionList.size() == 0) {

			final Guard newGuardFalse = new Guard();
			newGuardFalse.changeTermType(TermType.FALSE);
			final ArrayList<Guard> guardList = new ArrayList<Guard>();
			guardList.add(newGuardFalse);
			newFinalConditionList.add(guardList);
		}
		unionFinalConditions.put(mNewInitialState, new FinalCondition(newFinalConditionList));

		//transitions
		final ArrayList<Transition<LETTER, STATE>> newTransitions = new ArrayList<Transition<LETTER, STATE>>();
		addNewUnionTransitions(mFstOperand, newTransitions, unionTransitions);
		addNewUnionTransitions(mSndOperand, newTransitions, unionTransitions);
		unionTransitions.put(mNewInitialState, newTransitions);

		//result
		final CountingAutomaton<LETTER, STATE> resultAutomaton = new CountingAutomaton<LETTER, STATE>(
				mServices,
				unionAlphabet,
				unionStates,
				unionCounter,
				unionInitialConditions,
				unionFinalConditions,
				unionTransitions);
		return resultAutomaton;
	}

	private void addNewUnionInitialConditions (final CountingAutomaton<LETTER, STATE> automaton, final Map<STATE, InitialCondition> unionInitialConditions) {

		for (final STATE state : automaton.getStates()) {

			final Guard newInitialGuard = new Guard();
			newInitialGuard.changeTermType(TermType.FALSE);
			final ArrayList<Guard> newGuardList = new ArrayList<Guard>();
			newGuardList.add(newInitialGuard);
			final ArrayList<ArrayList<Guard>> newInitialConditionList = new ArrayList<ArrayList<Guard>>();
			newInitialConditionList.add(newGuardList);
			unionInitialConditions.put(state, new InitialCondition(newInitialConditionList));
		}
	}

	private void addNewUnionFinalConditions (final CountingAutomaton<LETTER, STATE> automaton, final ArrayList<ArrayList<Guard>> newFinalConditionList, final Map<STATE, FinalCondition> unionFinalConditions) {

		for (final STATE state : automaton.getStates()) {

			unionFinalConditions.put(state, automaton.getFinalConditions().get(state).copyFinalCondition());

			if (automaton.getInitialConditions().get(state).getCondition().get(0).get(0).getTermType() != TermType.FALSE &&
					automaton.getFinalConditions().get(state).getCondition().get(0).get(0).getTermType() != TermType.FALSE) {

				final ConjunctGuards conjunction = new ConjunctGuards(
						automaton.getFinalConditions().get(state).copyFinalCondition().getCondition(),
						automaton.getInitialConditions().get(state).copyInitialCondition().getCondition());
				newFinalConditionList.addAll(conjunction.getResult());
			}
		}
	}

	private void addNewUnionTransitions (final CountingAutomaton<LETTER, STATE> automaton, final ArrayList<Transition<LETTER, STATE>> newTransitions, final Map<STATE, ArrayList<Transition<LETTER, STATE>>> unionTransitions) {

			for (final STATE state : automaton.getStates()) {

				final ArrayList<Transition<LETTER, STATE>> transitionList = new ArrayList<Transition<LETTER, STATE>>();
				for (final Transition<LETTER, STATE> transition : automaton.getTransitions().get(state)) {
					final Transition<LETTER, STATE> transitionCopy = transition.copyTransition();
					transitionList.add(transitionCopy);
				}
				unionTransitions.put(state, transitionList);

				if (automaton.getInitialConditions().get(state).getCondition().get(0).get(0).getTermType() != TermType.FALSE) {

					for (final Transition<LETTER, STATE> transition : automaton.getTransitions().get(state)) {

						final Transition<LETTER, STATE> transitionCopy = transition.copyTransition();
						final ConjunctGuards conjunction = new ConjunctGuards(transitionCopy.getGuards(), automaton.getInitialConditions().get(state).copyInitialCondition().getCondition());
						final Transition<LETTER, STATE> newTransition = new Transition<LETTER, STATE>(
								transitionCopy.getLetter(),
								mNewInitialState,
								transitionCopy.getSucState(),
								conjunction.getResult(),
								transitionCopy.getUpdates());
						newTransitions.add(newTransition);
				}
			}
		}
	}

	@Override
	public CountingAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return true;
	}
}
