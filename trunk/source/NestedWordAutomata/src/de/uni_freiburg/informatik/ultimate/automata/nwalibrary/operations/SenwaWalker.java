package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.TestFileWriter;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.Senwa;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

import org.apache.log4j.Logger;

/**
 * Visit all states of a SENWA. This can also be used to construct this SEVPA.
 */
public class SenwaWalker<LETTER,STATE> {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	
	protected Senwa<LETTER,STATE> m_TraversedSenwa;

	
	/**
	 * STATEs that are already known but have not yet been visited.
	 */
	private final List<STATE> m_Worklist = new LinkedList<STATE>();
	
	/**
	 * STATEs that have already been marked. (Which means already visited or in
	 * the worklist.)
	 */
	private final Set<STATE> m_Marked = new HashSet<STATE>();
	
	
	/**
	 * We remove afterwards all dead ends iff set to true.
	 */
	protected boolean m_RemoveDeadEnds;
	
	/**
	 * We remove afterwards all non-live states iff set to true.
	 */
	protected boolean m_RemoveNonLiveStates = false;
	
	
	/**
	 * DoubleDeckers that have been constructed but do not occur in any
	 * accepting run of the automaton.
	 */
	private Map<STATE,Set<STATE>> m_RemovedDoubleDeckers = new HashMap<STATE,Set<STATE>>();
	
	/**
	 * DoubleDeckers which occur on an accepting run.
	 */
	protected Set<DoubleDecker<STATE>> doubleDeckersThatCanReachFinal;
	protected Map<STATE,STATE> m_CallSuccOfRemovedDown;
	
	/**
	 * 
	 */
	protected DoubleDecker<STATE> auxilliaryEmptyStackDoubleDecker;
	
	protected ISuccessorVisitor<LETTER, STATE> m_SuccVisit;
	private long m_DeadEndRemovalTime;
	
	public SenwaWalker (Senwa<LETTER,STATE> senwa, ISuccessorVisitor<LETTER, STATE> succVisit, boolean removeDeadEnds) throws OperationCanceledException {
		m_TraversedSenwa = senwa;
		m_SuccVisit = succVisit;
		m_RemoveDeadEnds = removeDeadEnds;
		traverseDoubleDeckerGraph();
	}
	

	
	public INestedWordAutomaton<LETTER,STATE> getResult() throws OperationCanceledException {
		return m_TraversedSenwa;
	}
	
	
	
	/**
	 * True iff the STATE state has been marked. A DoubleDecker
	 * is marked iff it has been visited or is in the m_Worklist.
	 */
	private final boolean wasMarked(STATE state) {
		return m_Marked.contains(state);
	}
	

	private final void mark(STATE state) {
		m_Marked.add(state);
	}
	
	
	
	/**
	 * Add STATE state to worklist if it has not yet been marked.
	 */
	private final void enqueueAndMark(STATE state) {
		assert m_TraversedSenwa.getStates().contains(state);
		if (!wasMarked(state)) {
			mark(state);
			m_Worklist.add(state);
		}
	}
	
	
//	/**
//	 * Record that summarySucc is reachable from summaryPred via a run over a
//	 * well-matched NestedWord.
//	 */
//	private final void addSummary(STATE summaryPred,
//							STATE summarySucc, STATE returnPred) {
//		Map<STATE,STATE> summarySuccessors = 
//			m_CallReturnSummary.get(summaryPred);
//		if (summarySuccessors == null) {
//			summarySuccessors = new HashMap<STATE,STATE>();
//			m_CallReturnSummary.put(summaryPred, summarySuccessors);
//		}
//		summarySuccessors.put(summarySucc, returnPred);
//		enqueueSummarySuccs(summaryPred, summarySucc, returnPred);
//	}
	


//	/**
//	 * For all DoubleDeckers (<i>down</i>,summaryPred) that have been marked
//	 * enqueue and mark the DoubleDecker (<i>down</i>,summarySucc) and record
//	 * that the DoubleDecker (summaryPred,returnPred) is a predecessor of
//	 * (<i>down</i>,summarySucc).
//	 */
//	private final void enqueueSummarySuccs(STATE summaryPred,
//			STATE summarySucc, STATE returnPred) {
//		for (STATE summaryPreDown : m_Marked_Up2Down.get(summaryPred)) {
//			DoubleDecker<STATE> doubleDecker = 
//				new DoubleDecker<STATE>(summaryPreDown, summaryPred);
//			DoubleDecker<STATE> summarySuccDoubleDecker = 
//				new DoubleDecker<STATE>(summaryPreDown, summarySucc);
//			DoubleDecker<STATE> summaryReturnPred = 
//				new DoubleDecker<STATE>(summaryPred, returnPred);
//			memorizePredecessor(summarySuccDoubleDecker, summaryReturnPred, m_ReturnPredecessors);
//			memorizePredecessor(summarySuccDoubleDecker, doubleDecker, m_SummaryPredecessors);
//			enqueueAndMark(summarySuccDoubleDecker);
//		}
//	}
//	
//	
//	
//	/**
//	 * Get all states <i>down</i> such that the DoubleDecker
//	 * (<i>down</i>,<i>up</i>) has been visited so far.
//	 */
//	private final Set<STATE> getKnownDownStates(STATE up) {
//		Set<STATE> downStates = m_Marked_Up2Down.get(up);
//		if (downStates == null) {
//			return new HashSet<STATE>(0);
//		}
//		else {
//			return downStates;
//		}
//	}
//	
//	/**
//	 * Get all states <i>up</i> such that the DoubleDecker
//	 * (<i>down</i>,<i>up</i>) has been visited so far.
//	 */
//	private final Set<STATE> getKnownUpStates(STATE up) {
//		if (m_Marked_Down2Up == null) {
//			throw new UnsupportedOperationException("Up states not computeted");
//		}
//		Set<STATE> upStates = m_Marked_Down2Up.get(up);
//		if (upStates == null) {
//			return new HashSet<STATE>(0);
//		}
//		else {
//			return upStates;
//		}
//	}

	
	protected final void traverseDoubleDeckerGraph() throws OperationCanceledException {
		Iterable<STATE> initialStates = m_SuccVisit.getInitialStates();
		for (STATE state : initialStates) {
			enqueueAndMark(state);
		}
		
		while(!m_Worklist.isEmpty()) {
			STATE state = m_Worklist.remove(0);
			assert m_TraversedSenwa.getStates().contains(state);
			
			Iterable<STATE> internalSuccs =	m_SuccVisit.visitAndGetInternalSuccessors(state);
			for (STATE succ : internalSuccs) {
				enqueueAndMark(succ);
			}
			Iterable<STATE> callSuccs = m_SuccVisit.visitAndGetCallSuccessors(state);
			for (STATE succ : callSuccs) {
				enqueueAndMark(succ);
				assert (succ == m_TraversedSenwa.getEntry(succ) || 
						m_TraversedSenwa.getEntry(succ) == null);
				ArrayList<STATE> moduleStates = new ArrayList<STATE>();
				moduleStates.addAll( m_TraversedSenwa.getModuleStates(succ));
				for (STATE moduleState : moduleStates) {
					Iterable<STATE> returnSuccs = 
							m_SuccVisit.visitAndGetReturnSuccessors(moduleState, state);
					for (STATE retSucc : returnSuccs) {
						enqueueAndMark(retSucc);
					}

				}
				assert m_TraversedSenwa.getCallPredecessors(succ).contains(state);
			}
			
			STATE entry = m_TraversedSenwa.getEntry(state);
			for (LETTER call : m_TraversedSenwa.lettersCallIncoming(entry)) {
				for (STATE hier : m_TraversedSenwa.predCall(entry, call)) {
					Iterable<STATE> returnSuccs = 
							m_SuccVisit.visitAndGetReturnSuccessors(state, hier);
					for (STATE retSucc : returnSuccs) {
						enqueueAndMark(retSucc);
					}
				}
			}
			
			if (!UltimateServices.getInstance().continueProcessing()) {
				throw new OperationCanceledException();
			}
			
			
		}
		s_Logger.info("Result " + m_TraversedSenwa.sizeInformation());
		if (m_RemoveDeadEnds && m_RemoveNonLiveStates) {
			throw new IllegalArgumentException("RemoveDeadEnds and RemoveNonLiveStates is set");
		}

		if (m_RemoveDeadEnds) {
//			new TestFileWriter(m_TraversedNwa, "TheAutomaotn", TestFileWriter.Labeling.TOSTRING);
			removeStatesThatCanNotReachFinal(false);
			if (m_TraversedSenwa.getInitialStates().isEmpty()) {
				assert m_TraversedSenwa.getStates().isEmpty();
				m_TraversedSenwa = getTotalizedEmptyAutomaton();
			}
			s_Logger.info("After removal of dead ends " + m_TraversedSenwa.sizeInformation());

		}
		if (m_RemoveNonLiveStates) {
//			s_Logger.warn("Minimize before non-live removal: " + 
//		((NestedWordAutomaton<LETTER,STATE>) (new MinimizeDfa<LETTER, STATE>(m_TraversedNwa)).getResult()).sizeInformation());
			removeNonLiveStates();
//			s_Logger.warn("Minimize after non-live removal: " + 
//		((NestedWordAutomaton<LETTER,STATE>) (new MinimizeDfa<LETTER, STATE>(m_TraversedNwa)).getResult()).sizeInformation());
			if (m_TraversedSenwa.getInitialStates().isEmpty()) {
				assert m_TraversedSenwa.getStates().isEmpty();
//				m_TraversedSenwa = getTotalizedEmptyAutomaton();
			}
			s_Logger.info("After removal of nonLiveStates " + m_TraversedSenwa.sizeInformation());
		}

		
	}
	
	protected Senwa<LETTER,STATE> getTotalizedEmptyAutomaton() {
		Senwa<LETTER,STATE> emptyAutomaton = new Senwa<LETTER,STATE>(
				m_TraversedSenwa.getInternalAlphabet(), 
				m_TraversedSenwa.getCallAlphabet(), 
				m_TraversedSenwa.getReturnAlphabet(), 
				m_TraversedSenwa.getStateFactory());
		STATE sinkState = emptyAutomaton.getStateFactory().createSinkStateContent();
		emptyAutomaton.addState(sinkState, true, false, sinkState);
		
		for (STATE state : emptyAutomaton.getStates()) {
			for (LETTER letter : emptyAutomaton.getInternalAlphabet()) {				
				if (emptyAutomaton.succInternal(state,letter).isEmpty()) {
					emptyAutomaton.addInternalTransition(state, letter, sinkState);
				}
			}
			for (LETTER letter : emptyAutomaton.getCallAlphabet()) {				
				if (emptyAutomaton.succCall(state,letter).isEmpty()) {
					emptyAutomaton.addCallTransition(state, letter, sinkState);
				}
			}
			for (LETTER symbol : emptyAutomaton.getReturnAlphabet()) {
				for (STATE hier : emptyAutomaton.getStates()) {
					if (emptyAutomaton.succReturn(state,hier,symbol).isEmpty()) {
						emptyAutomaton.addReturnTransition(state, hier, symbol, sinkState);
					}
				}
			}
		}

		return emptyAutomaton;
	}

	


	
	
	
	private final Set<STATE> computeStatesThatCanNotReachFinal() {
		
		// Set used to compute the states that can never reach the final state
		// initialized with all states and narrowed by the algorithm
		Set<STATE> statesNeverReachFinal = new HashSet<STATE>(m_TraversedSenwa.getStates());

//		Set<DoubleDecker<STATE>> acceptingDoubleDeckers = new HashSet<DoubleDecker<STATE>>();
//		for (STATE finalState : m_TraversedSenwa.getFinalStates()) {
//			Set<STATE> finalsDownStates = m_Marked_Up2Down.get(finalState);
//			for (STATE downStatesOfFinal : finalsDownStates) {
//				DoubleDecker<STATE> summary =	new DoubleDecker<STATE>(downStatesOfFinal, finalState);
//				acceptingDoubleDeckers.add(summary);
//			}
//		}
		
		LinkedList<STATE> ancestorSearchWorklist;
		
		//Computation of nonReturnAncestors
		ancestorSearchWorklist = new LinkedList<STATE>();
		for (STATE state : m_TraversedSenwa.getFinalStates()) {
			statesNeverReachFinal.remove(state);
		}
		ancestorSearchWorklist.addAll(m_TraversedSenwa.getFinalStates());
		while (!ancestorSearchWorklist.isEmpty()) {
			STATE state = ancestorSearchWorklist.removeFirst();
			statesNeverReachFinal.remove(state);
			for (LETTER letter: m_TraversedSenwa.lettersInternalIncoming(state)) {
				for (STATE pred : m_TraversedSenwa.predInternal(state, letter)) {
					boolean wasContained = statesNeverReachFinal.remove(pred);
					if (wasContained) {
						ancestorSearchWorklist.add(pred);
					}
				}
			}
			for (LETTER letter: m_TraversedSenwa.lettersCallIncoming(state)) {
				for (STATE pred : m_TraversedSenwa.predCall(state, letter)) {
					boolean wasContained = statesNeverReachFinal.remove(pred);
					if (wasContained) {
						ancestorSearchWorklist.add(pred);
					}
				}
			}
			for (LETTER letter: m_TraversedSenwa.lettersReturnIncoming(state)) {
				for (STATE hier : m_TraversedSenwa.predReturnHier(state, letter)) {
					for (STATE pred : m_TraversedSenwa.predReturnLin(state, letter, hier)) {
						boolean wasContained = statesNeverReachFinal.remove(pred);
						if (wasContained) {
							ancestorSearchWorklist.add(pred);
						}
					}
				}
			}
		}
		return statesNeverReachFinal;
	}
	
	
	
	/**
	 * Remove in the resulting automaton all states that can not reach a final
	 * state.
	 * @param computeRemovedDoubleDeckersAndCallSuccessors compute the set of 
	 * all DoubleDeckers which occurred in the build automaton but are not
	 * reachable after the removal 
	 * @return true iff at least one state was removed.
	 */
	public final boolean removeStatesThatCanNotReachFinal(
			boolean computeRemovedDoubleDeckersAndCallSuccessors) {
		long startTime = System.currentTimeMillis();
		Set<STATE> statesNeverReachFinal = computeStatesThatCanNotReachFinal();
		if (computeRemovedDoubleDeckersAndCallSuccessors) {
			announceRemovalOfDoubleDeckers(statesNeverReachFinal);
		}
		
//		//some states are not removed but loose inital property
//		Set<STATE> statesThatShouldNotBeInitialAnyMore = new HashSet<STATE>();
//		for (STATE state : m_TraversedSenwa.getInitialStates()) {
//			if (statesNeverReachFinal.contains(state)) {
//				continue;
//			}
//			DoubleDecker<STATE> dd = new DoubleDecker<STATE>(m_TraversedSenwa.getEmptyStackState(), state);
//			if (doubleDeckersThatCanReachFinal.contains(dd)) {
//				continue;
//			}
//			statesThatShouldNotBeInitialAnyMore.add(state);
//		}
//		for (STATE state : statesThatShouldNotBeInitialAnyMore) {
//			m_TraversedSenwa.makeStateNonIntial(state);
//			s_Logger.warn("The following state is not final any more: " +state);
//		}
		
		// remove states which can not reach final, but postpone removal of
		// entrys and remove them at last.
		Collection<STATE> entrysNeverReachFinal = new ArrayList<STATE>();
		for (STATE state : statesNeverReachFinal) {
			if (m_TraversedSenwa.isEntry(state)) {
				entrysNeverReachFinal.add(state);
			} else {
				m_TraversedSenwa.removeState(state);
			}
		}
		for (STATE state : entrysNeverReachFinal) {
			m_TraversedSenwa.removeState(state);
		}
		
		boolean atLeastOneStateRemoved = !statesNeverReachFinal.isEmpty();
		m_DeadEndRemovalTime += (System.currentTimeMillis() - startTime);
		return atLeastOneStateRemoved;
	}
	

	/**
	 * Announce removal of all DoubleDeckers (<i>down</i>,<i>up</i>) such that
	 * <i>down</i> or <i>up</i> is contained in statesGoingToBeRemoved.
	 */
	// _before_ because on removal we want to be able to access all states
	// of the automaton
	private void announceRemovalOfDoubleDeckers(Set<STATE> statesGoingToBeRemoved) {
		m_CallSuccOfRemovedDown = new HashMap<STATE,STATE>();		

		/**
		 * DoubleDeckers that have been constructed but do not occur in any
		 * accepting run of the automaton.
		 */
		for (STATE up : statesGoingToBeRemoved) {
			STATE entry = m_TraversedSenwa.getEntry(up);
			for (STATE down : m_TraversedSenwa.getCallPredecessors(entry)) {
				Set<STATE> downStates = m_RemovedDoubleDeckers.get(up);
				if (downStates == null) {
					downStates = new HashSet<STATE>();
					m_RemovedDoubleDeckers.put(up, downStates);
				}
				downStates.add(down);

				Set<STATE> downCallSuccs = computeState2CallSuccs(down);
				if (downCallSuccs.size() > 1) {
					throw new UnsupportedOperationException("If state has" +
							" several outgoing call transitions Hoare annotation might be incorrect.");
				} else if (downCallSuccs.size() == 1){
					STATE callSucc = downCallSuccs.iterator().next();
					m_CallSuccOfRemovedDown.put(down, callSucc);
				} else {
					assert downCallSuccs.isEmpty();
				}
			}
		}
	}
	
	
	
	/**
	 * Compute call successors for a given set of states.
	 */
	private Set<STATE> computeState2CallSuccs(STATE state) {
		Set<STATE> callSuccs = new HashSet<STATE>();
		if (state != m_TraversedSenwa.getEmptyStackState()) {
			for (LETTER letter : m_TraversedSenwa.lettersCall(state)) {
				callSuccs.addAll(m_TraversedSenwa.succCall(state, letter));
			}
		}
		return callSuccs;
	}
	
	
	


	
	
	/**
	 * Return true iff state has successors
	 */
	private boolean hasSuccessors(STATE state) {
		for (LETTER symbol : m_TraversedSenwa.lettersInternal(state)) {
			if (!m_TraversedSenwa.succInternal(state, symbol).isEmpty()) {
				return true;
			}
		}
		for (LETTER symbol : m_TraversedSenwa.lettersCall(state)) {
			if (!m_TraversedSenwa.succCall(state, symbol).isEmpty()) {
				return true;
			}
		}
		for (LETTER symbol : m_TraversedSenwa.lettersReturn(state)) {
			for (STATE hier : m_TraversedSenwa.hierPred(state, symbol)) {
				if (!m_TraversedSenwa.succReturn(state, hier, symbol).isEmpty()) {
					return true;
				}
			}
		}
		return false;
	}


	/**
	 * Remove all state that are accepting and do not have any successor.
	 * @return true iff some state was removed
	 */
	private final boolean removeAcceptingStatesWithoutSuccessors() {

		ArrayList<STATE> finalStatesWithoutSuccessor = new ArrayList<STATE>();
		for (STATE accepting : m_TraversedSenwa.getFinalStates()) {
			if (!hasSuccessors(accepting)) {
				finalStatesWithoutSuccessor.add(accepting);
			}
		}
		boolean atLeastOneStateRemoved = !finalStatesWithoutSuccessor.isEmpty();
		for (STATE finalStateWithoutSuccessor : finalStatesWithoutSuccessor) {
			m_TraversedSenwa.removeState(finalStateWithoutSuccessor);	
		}		
		return atLeastOneStateRemoved;
	}
	
	
	/**
	 * Remove all states from which only finitely many accepting states are
	 * reachable.
	 */
	private final void removeNonLiveStates() {
		boolean stateRemovedInInteration;
		do {
			stateRemovedInInteration = removeStatesThatCanNotReachFinal(false);
			stateRemovedInInteration |= removeAcceptingStatesWithoutSuccessors();
		} while (stateRemovedInInteration);
	}



	public Map<STATE,STATE> getCallSuccOfRemovedDown() {
		if (m_CallSuccOfRemovedDown == null || m_RemovedDoubleDeckers == null) {
			throw new AssertionError("Request computation when removing");
		}
		return m_CallSuccOfRemovedDown;
	}



	public Map<STATE,Set<STATE>> getRemovedDoubleDeckers() {
		if (m_CallSuccOfRemovedDown == null || m_RemovedDoubleDeckers == null) {
			throw new AssertionError("Request computation when removing");
		}
		return m_RemovedDoubleDeckers;
	}
	
	public interface ISuccessorVisitor<LETTER, STATE> {
		
		/**
		 * @return initial states of automaton
		 */
		public Iterable<STATE> getInitialStates();

		/**
		 * @return internal successors of doubleDeckers up state
		 */
		public Iterable<STATE> visitAndGetInternalSuccessors(STATE state);

		/**
		 * @return call successors of doubleDeckers up state
		 */
		public Iterable<STATE> visitAndGetCallSuccessors(STATE state);


		/**
		 * @return return successors of doubleDeckers up state
		 */
		public Iterable<STATE> visitAndGetReturnSuccessors(STATE state, STATE hier);

	}
	
	public long getDeadEndRemovalTime() {
		return m_DeadEndRemovalTime;
	}

	
	
}
