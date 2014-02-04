/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.AbstractAcceptance;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


/**
 * Class that provides the Buchi acceptance check for nested word automata. 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER> Symbol. Type of the symbols used as alphabet.
 * @param <STATE> Content. Type of the labels ("the content") of the automata states. 
 */
public class BuchiAccepts<LETTER,STATE> extends AbstractAcceptance<LETTER,STATE>
									    implements IOperation<LETTER,STATE> {
	
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	/**
	 * stem of the nested lasso word whose acceptance is checked 
	 */
	NestedWord<LETTER> m_Stem;
	
	/**
	 * loop of the nested lasso word whose acceptance is checked 
	 */
	NestedWord<LETTER> m_Loop;
	
	
	private final INestedWordAutomatonOldApi<LETTER,STATE> m_Nwa;
	private boolean m_Accepted;

	


	@Override
	public String operationName() {
		return "buchiAccepts";
	}
	
	

	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + m_Nwa.sizeInformation() 
				+ " Stem has " + m_Stem.length() + " letters." 
				+ " Loop has " + m_Loop.length() + " letters.";
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName();
	}




	@Override
	public Boolean getResult() {
		return m_Accepted;
	}


	/**
	 * Check if a Buchi nested word automaton accepts a nested lasso word. 
	 * @param nlw NestedLassoWord whose acceptance is checked
	 * @param nwa NestedWordAutomaton which is interpreted as Buchi nested word
	 * automaton here
	 * @return true iff nlw is accepted by nwa. Note that here a nested lasso word is
	 *  always rejected its loop contains pending returns.  
	 * @throws OperationCanceledException 
	 */
	public BuchiAccepts(INestedWordAutomatonOldApi<LETTER,STATE> nwa, NestedLassoWord<LETTER> nlw) throws OperationCanceledException{
		m_Nwa = nwa;
		
		m_Stem = nlw.getStem();
		m_Loop = nlw.getLoop();
		
		s_Logger.info(startMessage());
		
		if (m_Stem.containsPendingReturns()) {
			s_Logger.warn("This implementation of Buchi acceptance rejects lasso" +
					" words, where the stem contains pending returns.");
			m_Accepted = false;
			return;
		}
		
		if (m_Loop.containsPendingReturns()) {
			s_Logger.warn("This implementation of Buchi acceptance rejects lasso" +
					" words, where the loop contains pending returns.");
			m_Accepted = false;
			return;

		}
		
		if (m_Loop.length() ==0) {
			s_Logger.debug("LassoWords with empty lasso are rejected by every Büchi" +
					" automaton");
			m_Accepted = false;
			return;
		}


		m_Accepted = buchiAccepts();
		s_Logger.info(exitMessage());
	}

	private boolean buchiAccepts() throws OperationCanceledException {
		// First compute all states in which the automaton can be after 
		// processing the stem and lasso^*
		// Honda denotes the part of the lasso where stem and loop are connected.
		// Therefore we call theses stats Honda states.
		Set<STATE> hondaStates;
		{
			Set<Stack<STATE>> currentConfigs = emptyStackConfiguration(m_Nwa.getInitialStates());
			for (int i = 0; i < m_Stem.length(); i++) {
				currentConfigs = successorConfigurations(currentConfigs, m_Stem, i,
						m_Nwa, false);
				if (!UltimateServices.getInstance().continueProcessing()) {
					throw new OperationCanceledException();
				}
			}
			hondaStates = getTopMostStackElemets(currentConfigs);
		}
	
		Set<STATE> newHondaStates = hondaStates;
		do {
			hondaStates.addAll(newHondaStates);
			Set<Stack<STATE>> currentConfigs = emptyStackConfiguration(hondaStates);
			for (int i = 0; i < m_Loop.length(); i++) {
				currentConfigs = successorConfigurations(
						currentConfigs, m_Loop, i, m_Nwa, false);
				if (!UltimateServices.getInstance().continueProcessing()) {
					throw new OperationCanceledException();
				}
			}
			newHondaStates = getTopMostStackElemets(currentConfigs);
		 } while (!hondaStates.containsAll(newHondaStates));
		
		for (STATE hondaState : hondaStates) {
			if (repeatedLoopLeadsAgainToHondaState(hondaState)) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Compute for each hondaState if processing m_Loop repeatedly can lead to
	 * a run that contains an accepting state and brings the automaton back to
	 * the honda state.
	 * @throws OperationCanceledException 
	 */
	private boolean repeatedLoopLeadsAgainToHondaState(STATE hondaState) throws OperationCanceledException {
		// Store in currentConfigsVisitedAccepting / currentConfigsNotVisitedAccepting
		// which configurations belong to a run which has already visited an
		// accepting state.
		Set<Stack<STATE>> currentConfigsVisitedAccepting;
		Set<Stack<STATE>> currentConfigsNotVisitedAccepting;
		// Store in visited state which states have been visited when we
		// returned to the honda (related problem executing loop is not
		// sufficient to reach honda, executing loop^k is sufficient)
		Set<STATE> visitedatHondaAccepting = new HashSet<STATE>();
		Set<STATE> visitedatHondaNonAccepting = new HashSet<STATE>();
		Set<STATE> singletonStateSet = new HashSet<STATE>();
		singletonStateSet.add(hondaState);
		Set<Stack<STATE>> singletonConfigSet = 
				emptyStackConfiguration(singletonStateSet);
		currentConfigsVisitedAccepting = 
				removeAcceptingConfigurations(singletonConfigSet, m_Nwa);
		currentConfigsNotVisitedAccepting = singletonConfigSet;
		while (!currentConfigsNotVisitedAccepting.isEmpty() || !currentConfigsVisitedAccepting.isEmpty()) {
			for (int i = 0; i < m_Loop.length(); i++) {
				currentConfigsVisitedAccepting = successorConfigurations(
						currentConfigsVisitedAccepting, m_Loop, i, m_Nwa, false);
				currentConfigsNotVisitedAccepting = successorConfigurations(
						currentConfigsNotVisitedAccepting, m_Loop, i, m_Nwa, false);
				Set<Stack<STATE>> justVisitedAccepting = 
						removeAcceptingConfigurations(currentConfigsNotVisitedAccepting, m_Nwa);
				currentConfigsVisitedAccepting.addAll(justVisitedAccepting);
				if (!UltimateServices.getInstance().continueProcessing()) {
					throw new OperationCanceledException();
				}
			}
			
			// since pending returns are not allowed we omit considering stack:
			// if state was visited at honda we do not need to analyze another 
			// run starting at this state. 
			removeAllWhoseTopmostElementIsOneOf(
								currentConfigsVisitedAccepting, visitedatHondaAccepting);
			removeAllWhoseTopmostElementIsOneOf(
							currentConfigsNotVisitedAccepting, visitedatHondaNonAccepting);
			
			Set<STATE> topmostAccepting = getTopMostStackElemets(currentConfigsVisitedAccepting);
			Set<STATE> topmostNonAccepting = getTopMostStackElemets(currentConfigsNotVisitedAccepting);
			if (topmostAccepting.contains(hondaState)) {
				return true;
			}
			visitedatHondaAccepting.addAll(topmostAccepting);
			visitedatHondaNonAccepting.addAll(topmostNonAccepting);
		}
		return false;
	}
	
	/**
	 * Remove all configurations whose topmost element is in states.
	 */
	private void removeAllWhoseTopmostElementIsOneOf(
						Set<Stack<STATE>> configurations, Set<STATE> states) {
		List<Stack<STATE>> removalCandidate = new ArrayList<Stack<STATE>>();
		for (Stack<STATE> config : configurations) {
			if (states.contains(config.peek())) {
				removalCandidate.add(config);
			}
		}
		for (Stack<STATE> config : removalCandidate) {
			configurations.remove(config);
		}
	}
	
	private Set<STATE> getTopMostStackElemets(Set<Stack<STATE>> configurations) {
		Set<STATE> result = new HashSet<STATE>();
		for (Stack<STATE> config : configurations) {
			result.add(config.peek());
		}
		return result;
	}
	
	
	/**
	 * Remove from the input all accepting configurations. Return all these
	 * configurations which were accepting.
	 */
	private Set<Stack<STATE>> removeAcceptingConfigurations(Set<Stack<STATE>> configurations,
			INestedWordAutomatonOldApi<LETTER,STATE> nwa) {
		Set<Stack<STATE>> acceptingConfigurations = new HashSet<Stack<STATE>>();
		for (Stack<STATE> config : configurations) {
			STATE state = config.peek();
			if (nwa.isFinal(state)) {
				acceptingConfigurations.add(config);
			}
		}
		for (Stack<STATE> config : acceptingConfigurations) {
			configurations.remove(config);
		}
		return acceptingConfigurations;
	}



	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}
	
	
}

