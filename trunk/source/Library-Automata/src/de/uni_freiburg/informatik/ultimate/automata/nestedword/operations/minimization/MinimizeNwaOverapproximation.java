/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsIncluded;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.TimeoutFlag;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Calls another minimization procedure and interrupts it after a certain time.<br>
 * Correspondingly, the result may not be language-preserving, but it is certainly an overapproximation of the input.
 * <p>
 * The user may pass additional automata such that the result does not recognize any of their words, assuming that the
 * operand did not recognize them.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class MinimizeNwaOverapproximation<LETTER, STATE> extends AbstractMinimizeNwaDd<LETTER, STATE> {
	/**
	 * Default timeout: 1 second.
	 */
	public static final int DEFAULT_TIMEOUT = 1_000;
	
	/**
	 * Basic constructor with default timeout.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	public MinimizeNwaOverapproximation(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory, final INestedWordAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, DEFAULT_TIMEOUT);
	}
	
	/**
	 * Basic constructor with given timeout.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @param time
	 *            time in milliseconds for the minimization to run
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	public MinimizeNwaOverapproximation(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory, final INestedWordAutomaton<LETTER, STATE> operand, final int time)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, null, false, time, Collections.emptyList());
	}
	
	/**
	 * Extended constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @param initialPartition
	 *            initial partition of states
	 * @param addMapOldState2newState
	 *            true iff map (old state -> new state) should be created
	 * @param time
	 *            time in milliseconds for the minimization to run
	 * @param forbiddenLanguages
	 *            automata whose accepted words should not be accepted by the result
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	public MinimizeNwaOverapproximation(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory, final INestedWordAutomaton<LETTER, STATE> operand,
			final Collection<Set<STATE>> initialPartition, final boolean addMapOldState2newState, final int time,
			final Collection<? extends INestedWordAutomatonSimple<LETTER, STATE>> forbiddenLanguages)
			throws AutomataOperationCanceledException {
		super(services, stateFactory, "MinimizeNwaOverapproximation", operand);
		final TimeoutFlag<LETTER, STATE> timeout = new TimeoutFlag<>(time);
		final MinimizeSevpa<LETTER, STATE> backgroundMinimizer = new MinimizeSevpa<>(services, operand,
				initialPartition, stateFactory, addMapOldState2newState, timeout);
		constructResult(backgroundMinimizer.getConstructionInterrupted(), backgroundMinimizer.getResult(),
				forbiddenLanguages, stateFactory);
	}
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Start testing correctness of " + operationName());
		}
		
		boolean correct;
		correct = new IsIncluded<LETTER, STATE>(mServices, stateFactory, mOperand, getResult()).getResult();
		assert correct;
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + operationName());
		}
		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, operationName() + "Failed",
					"The result recognizes less words than before.", mOperand);
		}
		return correct;
	}
	
	private void constructResult(final boolean wasInterrrupted,
			final INestedWordAutomaton<LETTER, STATE> minimizerResult,
			final Collection<? extends INestedWordAutomatonSimple<LETTER, STATE>> forbiddenLanguages,
			final IStateFactory<STATE> stateFactoryIntersect)
			throws AutomataOperationCanceledException {
		if (!wasInterrrupted || forbiddenLanguages.isEmpty() || mOperand.size() == minimizerResult.size()) {
			// no special handling necessary
			directResultConstruction(minimizerResult);
			return;
		}
		
		minimizeWithDifferenceRefinement(minimizerResult, forbiddenLanguages, stateFactoryIntersect);
	}
	
	/**
	 * Uses a standard minimization which is interrupted when the time is up. Afterward it checks that the intersection
	 * of the result with each of the forbidden automata is empty. If not, the result is refined by taking the
	 * difference of the two automata.
	 */
	private void minimizeWithDifferenceRefinement(final INestedWordAutomaton<LETTER, STATE> minimizerResult,
			final Collection<? extends INestedWordAutomatonSimple<LETTER, STATE>> forbiddenLanguages,
			final IStateFactory<STATE> stateFactoryIntersect)
			throws AutomataOperationCanceledException, AssertionError {
		INestedWordAutomaton<LETTER, STATE> refinedResult = minimizerResult;
		
		for (final INestedWordAutomatonSimple<LETTER, STATE> automaton : forbiddenLanguages) {
			final INestedWordAutomaton<LETTER, STATE> intersection;
			try {
				intersection =
						new Intersect<LETTER, STATE>(mServices, stateFactoryIntersect, refinedResult, automaton)
								.getResult();
			} catch (final AutomataOperationCanceledException e) {
				throw e;
			} catch (final AutomataLibraryException e) {
				throw new AssertionError(e.getMessage());
			}
			
			if (!new IsEmpty<>(mServices, intersection).getResult()) {
				try {
					// refine current result
					refinedResult =
							new Difference<LETTER, STATE>(mServices, stateFactoryIntersect, refinedResult, automaton)
									.getResult();
				} catch (final AutomataOperationCanceledException e) {
					throw e;
				} catch (final AutomataLibraryException e) {
					throw new AssertionError(e.getMessage());
				}
			}
		}
		if (refinedResult.size() >= mOperand.size()) {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("Minimization did not decrease the size.");
			}
			directResultConstruction(mOperand);
		} else {
			directResultConstruction(refinedResult);
		}
	}
}
