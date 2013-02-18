package local.stalin.automata.nwalibrary.buchiNwa;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import local.stalin.automata.Activator;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.core.api.StalinServices;


/**
 * Class that provides the Buchi acceptance check for nested word automata. 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <S> Symbol. Type of the symbols used as alphabet.
 * @param <C> Content. Type of the labels ("the content") of the automata states. 
 */
public class AcceptanceCheck<S,C> {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	/**
	 * stem of the nested lasso word whose acceptance is checked 
	 */
	NestedWord<S> m_Stem;
	
	/**
	 * loop of the nested lasso word whose acceptance is checked 
	 */
	NestedWord<S> m_Loop;
	
	/**
	 * Check if a Buchi nested word automaton accepts a nested lasso word. 
	 * @param nlw NestedLassoWord whose acceptance is checked
	 * @param nwa NestedWordAutomaton which is interpreted as Buchi nested word
	 * automaton here
	 * @return true iff nlw is accepted by nwa. Note that here a nested lasso word is
	 *  always rejected its loop contains pending returns.  
	 */
	public boolean accepts(
			NestedLassoWord<S> nlw,
			INestedWordAutomaton<S,C> nwa){
		
		m_Stem = nlw.getStem();
		m_Loop = nlw.getLoop();
		
		if (m_Stem.containsPendingReturns()) {
			s_Logger.warn("This implementation of Buchi acceptance rejects lasso" +
					" words, where the stem contains pending returns.");
			return false;
		}
		
		if (m_Loop.containsPendingReturns()) {
			s_Logger.warn("This implementation of Buchi acceptance rejects lasso" +
					" words, where the loop contains pending returns.");
			return false;
		}
		
		if (m_Loop.length() ==0) {
			s_Logger.debug("LassoWords with empty lasso are rejected by every Büchi" +
					" automaton");
			return false;
		}

		// First compute all states in which the automaton can be after processing the
		// stem. 
		// Honda denotes the part of the lasso where stem and loop are connected.
		// Therefore we call theses stats Honda states.
		Set<IState<S,C>> hondaStates = new HashSet<IState<S,C>>();
		Collection<IState<S,C>> InitialStates = nwa.getInitialStates();
		for (IState<S,C> initialState : InitialStates) {
			Set<IState<S, C>> reach = 
				getReachableStates(0, initialState, new LinkedList<IState<S,C>>());
			hondaStates.addAll(reach);
		}
		
		// Compute for each hondaState if processing m_Loop can lead to a run that
		// contains an accepting state and brings the automaton back to the honda state.
		boolean result = false;
		for (IState<S,C> hondaState : hondaStates) {
			result = result || isCompleteableToAcceptingRun(
					hondaState, 
					0, 
					hondaState, 
					hondaState.isFinal(), 
					new LinkedList<IState<S,C>>());
		}
		return result;
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
	
	Set<IState<S,C>> getReachableStates(
			int currentPosition,
			IState<S,C> currentState,
			List<IState<S,C>> callStack) {
		if (currentPosition >= m_Stem.length()) {
			Set<IState<S,C>> result = new HashSet<IState<S,C>>();
			result.add(currentState);
			return result;
		}
		else {
			S currentSymbol = m_Stem.getSymbolAt(currentPosition);

			Collection<IState<S,C>> succStatesCollection;
			if (m_Stem.isInternalPosition(currentPosition)) {
				succStatesCollection =currentState.getInternalSucc(currentSymbol);
			}
			else if (m_Stem.isCallPosition(currentPosition)) {
				callStack.add(currentState);
				succStatesCollection = currentState.getCallSucc(currentSymbol);
			}
			else if (m_Stem.isReturnPosition(currentPosition)) {
				assert (!callStack.isEmpty()) : "restricted to stem without pending return";
				//pop the top element from the callStack
				IState<S,C> linearPred = callStack.remove(callStack.size()-1);
				succStatesCollection = 
					currentState.getReturnSucc(linearPred, currentSymbol);
			}
			else {
				throw new IllegalArgumentException();
			}

			if (succStatesCollection.isEmpty()) {
				return new HashSet<IState<S,C>>();
			}

			else{
				@SuppressWarnings("unchecked")
				IState<S,C>[] succStates = succStatesCollection.toArray(new IState[0]);
				Set<IState<S,C>> result = new HashSet<IState<S,C>>();
				for (int i=0; i<succStates.length; i++) {
					// in case of nondeterminism, i.e. several successor states for 
					// currentSymbol, every recursive call of this procedure needs its own
					// copy of the call stack. One of the recursive procedure calls (I decided 
					// for the last one) can use the existing copy  of the callStack. 
					List<IState<S,C>> callStackcopy;
					if (i!= succStates.length-1) {
						callStackcopy = new LinkedList<IState<S,C>>(callStack);
					}
					else {
						callStackcopy = callStack;
					}
					Set<IState<S, C>> returnValue = getReachableStates(
							currentPosition+1, 
							succStates[i], 
							callStackcopy);
					result.addAll(returnValue);
				}
				return result;
			}
		}		
	}
	
	
	
	
	
	/**
	 * Recursive check for an accepting loop run for the NestedWord m_Loop.
	 * <p>
	 * Assume,
	 *  <ul>
	 *  <li> we started processing m_Loop in state hondaState,
	 *  <li> we processed m_Loop until position currentPosition
	 *  <li> and ended in state currentState,
	 *  <li> while processing, we visited an accepting state iff visited Accepting is true
	 *  <li> while processing, we pushed the current state to callStack whenever we
	 *  processed a call position and pop'ed the top element from the callStack whenever
	 *  we processed a return position. 
	 *  </ul>
	 *  isCompleteableToAcceptingRun gives an answer to the question if processing 
	 *  m_Loop further can (nondeterminism! We have to check all posibilites) lead to
	 *  hondaState such that an accepting state was visited.
	 */
	boolean isCompleteableToAcceptingRun(
			IState<S,C> hondaState,
			int currentPosition,
			IState<S,C> currentState,
			boolean visitedAccepting,
			List<IState<S,C>> callStack) {
		
		if (currentPosition >= m_Loop.length() && currentPosition != 0) {
			if (currentState == hondaState && visitedAccepting) {
				return true;
			}
			else {
				return false;
			}
		}
		else {
			S currentSymbol = m_Loop.getSymbolAt(currentPosition);

			Collection<IState<S,C>> succStatesCollection;
			if (m_Loop.isInternalPosition(currentPosition)) {
				succStatesCollection =currentState.getInternalSucc(currentSymbol);
			}
			else if (m_Loop.isCallPosition(currentPosition)) {
				callStack.add(currentState);
				succStatesCollection = currentState.getCallSucc(currentSymbol);
			}
			else if (m_Loop.isReturnPosition(currentPosition)) {
				assert (!callStack.isEmpty()) : "restricted to loop without pending return";
				//pop the top element from the callStack
				IState<S,C> linearPred = callStack.remove(callStack.size()-1);
				succStatesCollection = 
					currentState.getReturnSucc(linearPred, currentSymbol);
			}
			else {
				throw new IllegalArgumentException();
			}

			if (succStatesCollection.isEmpty()) {
				return false;
			}
			else{
				@SuppressWarnings("unchecked")
				IState<S,C>[] succStates = succStatesCollection.toArray(new IState[0]);
				boolean result = false;
				for (int i=0; i<succStates.length; i++) {
					// in case of nondeterminism, i.e. several successor states for 
					// currentSymbol, every recursive call of this procedure needs its own
					// copy of the call stack. One of the recursive procedure calls (I decided 
					// for the last one) can use the existing copy  of the callStack. 
					List<IState<S,C>> callStackCopy;
					if (i!= succStates.length-1) {
						callStackCopy = new LinkedList<IState<S,C>>(callStack);
					}
					else {
						callStackCopy = callStack;
					}

					result = result || isCompleteableToAcceptingRun(
							hondaState, 
							currentPosition+1, 
							succStates[i], 
							visitedAccepting || succStates[i].isFinal(), 
							callStackCopy);
				}
				return result;
			}
		}
	}
	
	
}

