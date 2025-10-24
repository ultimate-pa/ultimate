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
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;

/**
 * Complement method for Counting Automata Needs a deterministic Automaton as Input
 *
 * @author Marcel Ebbinghaus
 * @author who is the author?
 */

public class Complement<LETTER, STATE, CRSF extends IStateFactory<STATE>> implements IOperation<LETTER, STATE, CRSF> {

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	private final CountingAutomaton<LETTER, STATE> mOperand;
	private final CountingAutomaton<LETTER, STATE> mResult;
	private final IIntersectionStateFactory<STATE> mStateFactory;

	public Complement(final AutomataLibraryServices services, final IIntersectionStateFactory<STATE> stateFactory,
			final CountingAutomaton<LETTER, STATE> operand) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(this.getClass());
		mOperand = operand;
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

		final ArrayList<Counter> complementCounter = new ArrayList<>();
		for (final Counter counter : mOperand.getCounter()) {
			complementCounter.add(counter.copyCounter());
		}
		final Map<STATE, InitialCondition> complementInitialConditions = new HashMap<>();
		final Map<STATE, FinalCondition> complementFinalConditions = new HashMap<>();
		final Map<STATE, ArrayList<Transition<LETTER, STATE>>> complementTransitions = new HashMap<>();

		for (final STATE state : mOperand.getStates()) {

			complementInitialConditions.put(state, mOperand.getInitialConditions().get(state).copyInitialCondition());
			final ArrayList<Transition<LETTER, STATE>> transitionList = new ArrayList<>();
			for (final Transition<LETTER, STATE> transition : mOperand.getTransitions().get(state)) {
				transitionList.add(transition.copyTransition());
			}
			complementTransitions.put(state, transitionList);

			final ArrayList<ArrayList<Guard>> finalConditionsCopy1 =
					mOperand.getFinalConditions().get(state).copyFinalCondition().getCondition();

			// negate guards
			for (final ArrayList<Guard> guardList : finalConditionsCopy1) {

				for (final Guard guard : guardList) {

					if (guard.getTermType() == TermType.TRUE) {

						guard.changeTermType(TermType.FALSE);
					} else if (guard.getTermType() == TermType.FALSE) {

						guard.changeTermType(TermType.TRUE);
					} else {

						switch (guard.getRelationSymbol()) {

						case EQ:
							guard.changeRelationType(RelationSymbol.DISTINCT);
							break;

						case DISTINCT:
							guard.changeRelationType(RelationSymbol.EQ);
							break;

						case LESS:
							guard.changeRelationType(RelationSymbol.GEQ);
							break;

						case GREATER:
							guard.changeRelationType(RelationSymbol.LEQ);
							break;

						case LEQ:
							guard.changeRelationType(RelationSymbol.GREATER);
							break;

						case GEQ:
							guard.changeRelationType(RelationSymbol.LESS);
							break;
						}
					}
				}
			}

			// transform back to DNF
			if (finalConditionsCopy1.size() == 1) {

				for (final Guard guard : finalConditionsCopy1.get(0)) {
					final ArrayList<Guard> guardList = new ArrayList<>();
					guardList.add(guard.copyGuard());
					finalConditionsCopy1.add(guardList);
				}
				finalConditionsCopy1.remove(0);
				complementFinalConditions.put(state, new FinalCondition(finalConditionsCopy1));
			} else {

				final ArrayList<ArrayList<Guard>> finalConditionsCopy2 = new ArrayList<>();
				final ArrayList<ArrayList<Guard>> finalConditionsCopy3 = new ArrayList<>();

				for (final Guard guard1 : finalConditionsCopy1.get(0)) {

					for (final Guard guard2 : finalConditionsCopy1.get(1)) {

						final ArrayList<Guard> tempCondition = new ArrayList<>();
						tempCondition.add(guard1.copyGuard());
						tempCondition.add(guard2.copyGuard());
						finalConditionsCopy3.add(tempCondition);
					}
				}
				finalConditionsCopy1.remove(0);
				finalConditionsCopy1.remove(0);

				while (finalConditionsCopy1.size() > 0) {

					for (final Guard guard1 : finalConditionsCopy1.get(0)) {

						for (final ArrayList<Guard> guardList : finalConditionsCopy3) {

							final ArrayList<Guard> tempCondition = new ArrayList<>();
							for (final Guard guard3 : guardList) {
								tempCondition.add(guard3.copyGuard());
							}
							tempCondition.add(guard1.copyGuard());
							finalConditionsCopy2.add(tempCondition);
						}
					}
					finalConditionsCopy3.clear();
					for (final ArrayList<Guard> list : finalConditionsCopy2) {
						finalConditionsCopy3.add(new ArrayList<>(list));
					}
					finalConditionsCopy1.remove(0);
					finalConditionsCopy2.clear();
				}
				complementFinalConditions.put(state, new FinalCondition(finalConditionsCopy3));
			}
		}

		// result
		final CountingAutomaton<LETTER, STATE> resultAutomaton =
				new CountingAutomaton<>(mServices, mOperand.getAlphabet(), mOperand.getStates(), complementCounter,
						complementInitialConditions, complementFinalConditions, complementTransitions);
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
