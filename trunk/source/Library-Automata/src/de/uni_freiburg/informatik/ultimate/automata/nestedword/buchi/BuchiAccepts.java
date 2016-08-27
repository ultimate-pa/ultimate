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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.AbstractAcceptance;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;


/**
 * Class that provides the Buchi acceptance check for nested word automata.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER> Symbol. Type of the symbols used as alphabet.
 * @param <STATE> Content. Type of the labels ("the content") of the automata states.
 */
public class BuchiAccepts<LETTER,STATE>
		extends AbstractAcceptance<LETTER,STATE>
		implements IOperation<LETTER,STATE> {
	/**
	 * stem of the nested lasso word whose acceptance is checked
	 */
	private NestedWord<LETTER> mStem;
	
	/**
	 * loop of the nested lasso word whose acceptance is checked
	 */
	private NestedWord<LETTER> mLoop;
	
	/**
	 * Check if a Buchi nested word automaton accepts a nested lasso word.
	 * 
	 * <p>Returns true iff nlw is accepted by nwa. Note that here a nested lasso
	 * word is always rejected if its loop contains pending returns.
	 * 
	 * @param services Ultimate services
	 * @param nlw NestedLassoWord whose acceptance is checked
	 * @param operand NestedWordAutomaton which is interpreted as Buchi nested word
	 *     automaton here
	 * @throws AutomataLibraryException if accept fails
	 */
	public BuchiAccepts(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER,STATE> operand,
			final NestedLassoWord<LETTER> nlw)
					throws AutomataLibraryException {
		super(services, operand);
		mStem = nlw.getStem();
		mLoop = nlw.getLoop();
		
		mLogger.info(startMessage());
		
		if (mStem.containsPendingReturns()) {
			mLogger.warn("This implementation of Buchi acceptance rejects lasso"
					+ " words, where the stem contains pending returns.");
			mIsAccepted = false;
			return;
		}
		
		if (mLoop.containsPendingReturns()) {
			mLogger.warn("This implementation of Buchi acceptance rejects lasso"
					+ " words, where the loop contains pending returns.");
			mIsAccepted = false;
			return;
		}
		
		if (mLoop.length() == 0) {
			mLogger.debug("LassoWords with empty lasso are rejected by every Büchi"
					+ " automaton");
			mIsAccepted = false;
			return;
		}

		mIsAccepted = buchiAccepts();
		mLogger.info(exitMessage());
	}

	@Override
	public String operationName() {
		return "buchiAccepts";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + mOperand.sizeInformation()
				+ " Stem has " + mStem.length() + " letters."
				+ " Loop has " + mLoop.length() + " letters.";
	}

	private boolean buchiAccepts() throws AutomataLibraryException {
		// First compute all states in which the automaton can be after
		// processing the stem and lasso^*
		// Honda denotes the part of the lasso where stem and loop are connected.
		// Therefore we call theses stats Honda states.
		Set<STATE> hondaStates;
		{
			Set<ArrayDeque<STATE>> currentConfigs = emptyStackConfiguration(mOperand.getInitialStates());
			for (int i = 0; i < mStem.length(); i++) {
				currentConfigs = successorConfigurations(currentConfigs, mStem, i,
						mOperand, false);
				if (isCancellationRequested()) {
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}
			hondaStates = getTopMostStackElemets(currentConfigs);
		}
	
		Set<STATE> newHondaStates = hondaStates;
		do {
			hondaStates.addAll(newHondaStates);
			Set<ArrayDeque<STATE>> currentConfigs = emptyStackConfiguration(hondaStates);
			for (int i = 0; i < mLoop.length(); i++) {
				currentConfigs = successorConfigurations(
						currentConfigs, mLoop, i, mOperand, false);
				if (isCancellationRequested()) {
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}
			newHondaStates = getTopMostStackElemets(currentConfigs);
		 } while (!hondaStates.containsAll(newHondaStates));
		
		for (final STATE hondaState : hondaStates) {
			if (repeatedLoopLeadsAgainToHondaState(hondaState)) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Compute for each hondaState if processing mLoop repeatedly can lead to
	 * a run that contains an accepting state and brings the automaton back to
	 * the honda state.
	 * @throws AutomataLibraryException if construction fails
	 */
	private boolean repeatedLoopLeadsAgainToHondaState(final STATE hondaState)
			throws AutomataLibraryException {
		// Store in currentConfigsVisitedAccepting / currentConfigsNotVisitedAccepting
		// which configurations belong to a run which has already visited an
		// accepting state.
		Set<ArrayDeque<STATE>> currentConfigsVisitedAccepting;
		Set<ArrayDeque<STATE>> currentConfigsNotVisitedAccepting;
		// Store in visited state which states have been visited when we
		// returned to the honda (related problem executing loop is not
		// sufficient to reach honda, executing loop^k is sufficient)
		final Set<STATE> visitedatHondaAccepting = new HashSet<STATE>();
		final Set<STATE> visitedatHondaNonAccepting = new HashSet<STATE>();
		final Set<STATE> singletonStateSet = new HashSet<STATE>();
		singletonStateSet.add(hondaState);
		final Set<ArrayDeque<STATE>> singletonConfigSet =
				emptyStackConfiguration(singletonStateSet);
		currentConfigsVisitedAccepting =
				removeAcceptingConfigurations(singletonConfigSet, mOperand);
		currentConfigsNotVisitedAccepting = singletonConfigSet;
		while (!currentConfigsNotVisitedAccepting.isEmpty() || !currentConfigsVisitedAccepting.isEmpty()) {
			for (int i = 0; i < mLoop.length(); i++) {
				currentConfigsVisitedAccepting = successorConfigurations(
						currentConfigsVisitedAccepting, mLoop, i, mOperand, false);
				currentConfigsNotVisitedAccepting = successorConfigurations(
						currentConfigsNotVisitedAccepting, mLoop, i, mOperand, false);
				final Set<ArrayDeque<STATE>> justVisitedAccepting =
						removeAcceptingConfigurations(currentConfigsNotVisitedAccepting, mOperand);
				currentConfigsVisitedAccepting.addAll(justVisitedAccepting);
				if (isCancellationRequested()) {
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}
			
			// since pending returns are not allowed we omit considering stack:
			// if state was visited at honda we do not need to analyze another
			// run starting at this state.
			removeAllWhoseTopmostElementIsOneOf(
								currentConfigsVisitedAccepting, visitedatHondaAccepting);
			removeAllWhoseTopmostElementIsOneOf(
							currentConfigsNotVisitedAccepting, visitedatHondaNonAccepting);
			
			final Set<STATE> topmostAccepting =
					getTopMostStackElemets(currentConfigsVisitedAccepting);
			if (topmostAccepting.contains(hondaState)) {
				return true;
			}
			final Set<STATE> topmostNonAccepting =
					getTopMostStackElemets(currentConfigsNotVisitedAccepting);
			visitedatHondaAccepting.addAll(topmostAccepting);
			visitedatHondaNonAccepting.addAll(topmostNonAccepting);
		}
		return false;
	}
	
	/**
	 * Remove all configurations whose topmost element is in states.
	 */
	private void removeAllWhoseTopmostElementIsOneOf(
						final Set<ArrayDeque<STATE>> configurations, final Set<STATE> states) {
		final List<ArrayDeque<STATE>> removalCandidate = new ArrayList<ArrayDeque<STATE>>();
		for (final ArrayDeque<STATE> config : configurations) {
			if (states.contains(config.peek())) {
				removalCandidate.add(config);
			}
		}
		for (final ArrayDeque<STATE> config : removalCandidate) {
			configurations.remove(config);
		}
	}
	
	private Set<STATE> getTopMostStackElemets(final Set<ArrayDeque<STATE>> configurations) {
		final Set<STATE> result = new HashSet<STATE>();
		for (final ArrayDeque<STATE> config : configurations) {
			result.add(config.peek());
		}
		return result;
	}
	
	/**
	 * Remove from the input all accepting configurations. Return all these
	 * configurations which were accepting.
	 */
	private Set<ArrayDeque<STATE>> removeAcceptingConfigurations(final Set<ArrayDeque<STATE>> configurations,
			final INestedWordAutomatonSimple<LETTER,STATE> nwa) {
		final Set<ArrayDeque<STATE>> acceptingConfigurations = new HashSet<ArrayDeque<STATE>>();
		for (final ArrayDeque<STATE> config : configurations) {
			final STATE state = config.peek();
			if (nwa.isFinal(state)) {
				acceptingConfigurations.add(config);
			}
		}
		for (final ArrayDeque<STATE> config : acceptingConfigurations) {
			configurations.remove(config);
		}
		return acceptingConfigurations;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		mLogger.warn("No test for BuchiAccepts available yet");
		return true;
	}
}

