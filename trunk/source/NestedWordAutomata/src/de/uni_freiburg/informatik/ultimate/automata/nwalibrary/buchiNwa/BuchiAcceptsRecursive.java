package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


/**
 * Class that provides the Buchi acceptance check for nested word automata. 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER> Symbol. Type of the symbols used as alphabet.
 * @param <STATE> Content. Type of the labels ("the content") of the automata states. 
 */
public class BuchiAcceptsRecursive<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	
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
	private final NestedLassoWord<LETTER> m_Nlw;
	private boolean m_Accepted;

	


	@Override
	public String operationName() {
		return "buchiAcceptsRecursive";
	}
	
	

	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Nwa.sizeInformation();
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
	 */
	public BuchiAcceptsRecursive(INestedWordAutomatonOldApi<LETTER,STATE> nwa, NestedLassoWord<LETTER> nlw){
		m_Nwa = nwa;
		m_Nlw = nlw;
		s_Logger.info(startMessage());
		
		m_Stem = nlw.getStem();
		m_Loop = nlw.getLoop();
		
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

		// First compute all states in which the automaton can be after processing the
		// stem. 
		// Honda denotes the part of the lasso where stem and loop are connected.
		// Therefore we call theses stats Honda states.
		Set<STATE> hondaStates = new HashSet<STATE>();
		Collection<STATE> InitialStates = nwa.getInitialStates();
		for (STATE initialState : InitialStates) {
			Set<STATE> reach = 
				getReachableStates(0, initialState, new LinkedList<STATE>());
			hondaStates.addAll(reach);
		}
		
		// Compute for each hondaState if processing m_Loop can lead to a run that
		// contains an accepting state and brings the automaton back to the honda state.
		boolean result = false;
		for (STATE hondaState : hondaStates) {
			result = result || isCompleteableToAcceptingRun(
					new HashMap<STATE,Boolean>(), 
					0, 
					hondaState, 
					new LinkedList<STATE>());
		}
		m_Accepted = result;
		s_Logger.info(exitMessage());
	}


	
	
	/**
	 * Recursive computation of reachable states while processing m_Stem.
	 * <p>
	 * Assume,
	 *  <ul>
	 *  <li> we started processing m_Stem in some state,
	 *  <li> we processed m_Stem until position currentPosition
	 *  <li> and ended in state currentState,
	 *  <li> while processing, we pushed the current state to callStack whenever we
	 *  processed a call position and pop'ed the top element from the callStack whenever
	 *  we processed a return position. 
	 *  </ul>
	 *  getReachableStates computes the states that we can reach by processing 
	 *  m_Stem further. If the automaton is deterministic this result will always be a
	 *   singleton.
	 */	
	
	Set<STATE> getReachableStates(
			int currentPosition,
			STATE currentState,
			List<STATE> callStack) {
		if (currentPosition >= m_Stem.length()) {
			Set<STATE> result = new HashSet<STATE>();
			result.add(currentState);
			return result;
		}
		else {
			LETTER currentSymbol = m_Stem.getSymbolAt(currentPosition);

			Iterable<STATE> succStatesCollection;
			if (m_Stem.isInternalPosition(currentPosition)) {
				succStatesCollection = m_Nwa.succInternal(currentState, currentSymbol);
			}
			else if (m_Stem.isCallPosition(currentPosition)) {
				callStack.add(currentState);
				succStatesCollection = m_Nwa.succCall(currentState, currentSymbol);
			}
			else if (m_Stem.isReturnPosition(currentPosition)) {
				assert (!callStack.isEmpty()) : "restricted to stem without pending return";
				//pop the top element from the callStack
				STATE linearPred = callStack.remove(callStack.size()-1);
				succStatesCollection = m_Nwa.succReturn(currentState, linearPred, currentSymbol);
			}
			else {
				throw new IllegalArgumentException();
			}

			if (!succStatesCollection.iterator().hasNext()) {
				return new HashSet<STATE>();
			}

			else{
				List<STATE> succStates = new ArrayList<STATE>();
				for (STATE succ : succStatesCollection) {
					succStates.add(succ);
				}
				Set<STATE> result = new HashSet<STATE>();
				for (int i=0; i<succStates.size(); i++) {
					// in case of nondeterminism, i.e. several successor states for 
					// currentSymbol, every recursive call of this procedure needs its own
					// copy of the call stack. One of the recursive procedure calls (I decided 
					// for the last one) can use the existing copy  of the callStack. 
					List<STATE> callStackcopy;
					if (i!= succStates.size()-1) {
						callStackcopy = new LinkedList<STATE>(callStack);
					}
					else {
						callStackcopy = callStack;
					}
					Set<STATE> returnValue = getReachableStates(
							currentPosition+1, 
							succStates.get(i), 
							callStackcopy);
					result.addAll(returnValue);
				}
				return result;
			}
		}		
	}
	
	
	
	
	
	/**
	 * Recursive check for an accepting loop run for the NestedWord m_Loop.
	 * Therefore we process m_Loop several times (see
	 * examples/Automata/BuchiNWA/BugAccepts). Before reading m_Loop, (again)
	 * we store the current state in hondaCandidates. Whenever a
	 * hondaCandidate was visited twice we terminate.
	 * <p>
	 * Assume,
	 *  <ul>
	 *  <li> before reading m_Loop, we have always been in one of the states
	 *  stored in the domain of hondaCandidates2visitedFinal,
	 *  <li> we processed m_Loop until position currentPosition
	 *  <li> and ended in state currentState,
	 *  <li> since visiting hondaState (for the first time) we visited an
	 *  accepting state, iff the image of hondateStates is true.
	 *  <li> while processing, we pushed the current state to callStack whenever
	 *   we processed a call position and pop'ed the top element from the
	 *   callStack whenever we processed a return position. 
	 *  </ul>
	 *  isCompleteableToAcceptingRun gives an answer to the question if
	 *  processing m_Loop further can (nondeterminism! We have to check all
	 *  possibilities) lead to hondaState such that an accepting state was
	 *  visited.
	 */
	boolean isCompleteableToAcceptingRun(
			Map<STATE,Boolean> hondaCandidates2visitedFinal,
			int currentPosition,
			STATE currentState,
			List<STATE> callStack) {
		assert ( currentPosition <= m_Loop.length());
		if (currentPosition == m_Loop.length()) {
			currentPosition = 0;
		}		
		if (currentPosition == 0) {
			if (hondaCandidates2visitedFinal.containsKey(currentState)) {
				return hondaCandidates2visitedFinal.get(currentState);
			}
			else {
				hondaCandidates2visitedFinal.put(currentState, false);
			}
		}
		if (m_Nwa.isFinal(currentState)) {
			for (STATE hondaCandidate : hondaCandidates2visitedFinal.keySet()) {
				hondaCandidates2visitedFinal.put(hondaCandidate, true);
			}
		}

		LETTER currentSymbol = m_Loop.getSymbolAt(currentPosition);

		Iterable<STATE> succStatesCollection;
		if (m_Loop.isInternalPosition(currentPosition)) {
			succStatesCollection = m_Nwa.succInternal(currentState, currentSymbol);
		}
		else if (m_Loop.isCallPosition(currentPosition)) {
			callStack.add(currentState);
			succStatesCollection = m_Nwa.succCall(currentState, currentSymbol);
		}
		else if (m_Loop.isReturnPosition(currentPosition)) {
			assert (!callStack.isEmpty()) : "restricted to loop without pending return";
			//pop the top element from the callStack
			STATE linearPred = callStack.remove(callStack.size()-1);
			succStatesCollection = m_Nwa.succReturn(currentState, linearPred, currentSymbol);
		}
		else {
			throw new IllegalArgumentException();
		}

		if (!succStatesCollection.iterator().hasNext()) {
			return false;
		}
		else{
			@SuppressWarnings("unchecked")
			List<STATE> succStates = new ArrayList<STATE>();
			for (STATE succ : succStatesCollection) {
				succStates.add(succ);
			}
			boolean result = false;
			for (int i=0; i<succStates.size(); i++) {
				// in case of nondeterminism, i.e. several successor states for 
				// currentSymbol, every recursive call of this procedure needs its own
				// copy of the call stack. One of the recursive procedure calls (I decided 
				// for the last one) can use the existing copy  of the callStack. 
				List<STATE> callStackCopy;
				Map<STATE, Boolean> hondaCandidatesCopy;
				if (i!= succStates.size()-1) {
					callStackCopy = new LinkedList<STATE>(callStack);
					hondaCandidatesCopy = new HashMap<STATE,Boolean>(
												hondaCandidates2visitedFinal);
				}
				else {
					callStackCopy = callStack;
					hondaCandidatesCopy = hondaCandidates2visitedFinal;
				}

				result = result || isCompleteableToAcceptingRun(
						hondaCandidatesCopy,
						currentPosition+1, 
						succStates.get(i), 
						callStackCopy);
			}
			return result;
		}
	}



	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}





	
	
}

