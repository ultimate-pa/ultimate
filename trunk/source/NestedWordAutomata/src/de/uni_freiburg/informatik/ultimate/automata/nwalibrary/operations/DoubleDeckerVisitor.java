package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.DoubleDeckerVisitor.ReachFinal;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

/**
 * TODO Documentation
 * 
 * TODO: Optimization: For most operations the internal and call successors of
 * (<i>down</i>,<i>up</i>) are the same for all down states. So a lot of
 * successors are computed several times, but you could see the already in 
 * m_TraversedNwa. Suggestion: Extension that implements
 * visitAndGetInternalSuccessors(DoubleDecker) and has abstract 
 * constructInternalSuccessors(IState) method.
 * 
 * @param <LETTER>
 * @param <STATE>
 */
public abstract class DoubleDeckerVisitor<LETTER,STATE> implements 
									IOpWithDelayedDeadEndRemoval<LETTER, STATE>{
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	public enum ReachFinal { UNKNOWN, AT_LEAST_ONCE  }
	
	
	protected INestedWordAutomaton<LETTER,STATE> m_TraversedNwa;


	/**
	 * We call a DoubleDecker marked if it has been visited or is contained in
	 * the worklist. The DoubleDecker (<i>down</i>,<i>up</i>) is marked iff 
	 * <i>down</i> is contained in the range of <i>up</i>.
	 */
	private final Map<STATE,Map<STATE, ReachFinal>> m_Marked_Up2Down = 
			new HashMap<STATE,Map<STATE, ReachFinal>>();


	/**
	 * DoubleDecker that are already known but have not yet been visited.
	 */
	private final List<DoubleDecker<STATE>> m_Worklist = 
		new LinkedList<DoubleDecker<STATE>>();
	
	
	/**
	 * Pairs of states (q,q') of the automaton such that q' is reachable from q
	 * via a well-matched nested word in which the first position is a call
	 * position and the last position is a return position. 
	 */
	private final Map<STATE,Map<STATE,STATE>> m_CallReturnSummary = 
			new HashMap<STATE,Map<STATE,STATE>>();
	

	/**
	 * We remove afterwards all dead ends iff set to true.
	 */
	protected boolean m_RemoveDeadEnds = false;
	
	/**
	 * We remove afterwards all non-live states iff set to true.
	 */
	protected boolean m_RemoveNonLiveStates = false;
	
	
	/**
	 * Compute the predecessors of all DoubleDeckers. Neccessary for removal
	 * of dead ends.
	 * TODO: Optimization make this optional for cases where we don't want to
	 * minimize.
	 */
	protected boolean m_ComputePredecessorDoubleDeckers = true;
	
	
//	/**
//	 * Predecessor DoubleDeckers under internal transitions.
//	 * Used only for removal of dead ends and non-live states.
//	 */
//	protected Map<DoubleDecker<STATE>,Set<DoubleDecker<STATE>>> m_InternalPredecessors =
//		new HashMap<DoubleDecker<STATE>,Set<DoubleDecker<STATE>>>();
//	/**
//	 * Predecessor DoubleDeckers under summary transitions.
//	 * Used only for removal of dead ends and non-live states.
//	 */
//	protected Map<DoubleDecker<STATE>,Set<DoubleDecker<STATE>>> m_SummaryPredecessors =
//		new HashMap<DoubleDecker<STATE>,Set<DoubleDecker<STATE>>>();
//	/**
//	 * Predecessor DoubleDeckers under call transitions.
//	 * Used only for removal of dead ends and non-live states.
//	 */
//	protected Map<DoubleDecker<STATE>,Set<DoubleDecker<STATE>>> m_CallPredecessors =
//		new HashMap<DoubleDecker<STATE>,Set<DoubleDecker<STATE>>>();
//	/**
//	 * Predecessor DoubleDeckers under call transitions.
//	 * Used only for removal of dead ends and non-live states.
//	 */
//	protected Map<DoubleDecker<STATE>,Set<DoubleDecker<STATE>>> m_ReturnPredecessors =
//		new HashMap<DoubleDecker<STATE>,Set<DoubleDecker<STATE>>>();

	
	
//	/**
//	 * DoubleDeckers that have been constructed but do not occur in any
//	 * accepting run of the automaton.
//	 */
//	private Map<STATE,Set<STATE>> m_RemovedDoubleDeckers = new HashMap<STATE,Set<STATE>>();
	
//	/**
//	 * DoubleDeckers which occur on an accepting run.
//	 */
////	protected Set<DoubleDecker<STATE>> doubleDeckersThatCanReachFinal;
//	protected Map<STATE,STATE> m_CallSuccOfRemovedDown;
	
	/**
	 * 
	 */
//	protected DoubleDecker<STATE> auxilliaryEmptyStackDoubleDecker;


	private long m_DeadEndRemovalTime;


private Set<STATE> m_DeadEnds;
	

	
	public INestedWordAutomaton<LETTER,STATE> getResult() throws OperationCanceledException {
		return m_TraversedNwa;
	}
	
	
	
	/**
	 * True iff the DoubleDecker doubleDecker has been marked. A DoubleDecker
	 * is marked iff it has been visited or is in the m_Worklist.
	 */
	private final boolean wasMarked(DoubleDecker<STATE> doubleDecker) {
		 Map<STATE, ReachFinal> downState = m_Marked_Up2Down.get(doubleDecker.getUp());
		if (downState == null) {
			return false;
		}
		else {
			return downState.containsKey(doubleDecker.getDown());
		}
	}
	

	private final void mark(DoubleDecker<STATE> doubleDecker) {
		Map<STATE, ReachFinal> downStates = m_Marked_Up2Down.get(doubleDecker.getUp());
		if (downStates == null) {
			downStates = new HashMap<STATE, ReachFinal>();
			m_Marked_Up2Down.put(doubleDecker.getUp(), downStates);
		}
		downStates.put(doubleDecker.getDown(),ReachFinal.UNKNOWN);
		
//		Set<STATE> upStates = m_Marked_Down2Up.get(doubleDecker.getDown());
//		if (upStates == null) {
//			upStates = new HashSet<STATE>();
//			m_Marked_Down2Up.put(doubleDecker.getDown(), upStates);
//		}
//		upStates.add(doubleDecker.getUp());
	}
	
	
	
	/**
	 * Add doubleDecker to worklist if it has not yet been marked.
	 */
	private final void enqueueAndMark(DoubleDecker<STATE> doubleDecker) {
		if (!wasMarked(doubleDecker)) {
			mark(doubleDecker);
			m_Worklist.add(doubleDecker);
		}
	}
	
	
//	/**
//	 * Record in predecessorMapping that preDoubleDecker is a predecessor of
//	 * doubleDecker.
//	 * predecessorMapping should be the mapping for either, call predecessors,
//	 * internal predecessors, summary predecessors or return predecesssors.
//	 */
//	private final void memorizePredecessor(
//			DoubleDecker<STATE> doubleDecker, 
//			DoubleDecker<STATE> preDoubleDecker,
//			Map<DoubleDecker<STATE>,Set<DoubleDecker<STATE>>> predecessorMapping) {
//		if (!m_ComputePredecessorDoubleDeckers) {
//			return;
//		}
//		assert ( predecessorMapping == m_CallPredecessors 
//			|| predecessorMapping == m_ReturnPredecessors
//			|| predecessorMapping == m_InternalPredecessors
//			|| predecessorMapping == m_SummaryPredecessors);
//		if (preDoubleDecker != null) {
//			Set<DoubleDecker<STATE>> predSet = predecessorMapping.get(doubleDecker);
//			if (predSet == null) {
//				predSet = new HashSet<DoubleDecker<STATE>>();
//				predecessorMapping.put(doubleDecker, predSet);
//			}
//			predSet.add(preDoubleDecker);
//		}
//	}
	
	
	/**
	 * Record that summarySucc is reachable from summaryPred via a run over a
	 * well-matched NestedWord.
	 */
	private final void addSummary(STATE summaryPred,
							STATE summarySucc, STATE returnPred) {
		Map<STATE,STATE> summarySuccessors = 
			m_CallReturnSummary.get(summaryPred);
		if (summarySuccessors == null) {
			summarySuccessors = new HashMap<STATE,STATE>();
			m_CallReturnSummary.put(summaryPred, summarySuccessors);
		}
		summarySuccessors.put(summarySucc, returnPred);
		enqueueSummarySuccs(summaryPred, summarySucc, returnPred);
	}
	


	/**
	 * For all DoubleDeckers (<i>down</i>,summaryPred) that have been marked
	 * enqueue and mark the DoubleDecker (<i>down</i>,summarySucc) and record
	 * that the DoubleDecker (summaryPred,returnPred) is a predecessor of
	 * (<i>down</i>,summarySucc).
	 */
	private final void enqueueSummarySuccs(STATE summaryPred,
			STATE summarySucc, STATE returnPred) {
		for (STATE summaryPreDown : m_Marked_Up2Down.get(summaryPred).keySet()) {
			DoubleDecker<STATE> doubleDecker = 
				new DoubleDecker<STATE>(summaryPreDown, summaryPred);
			DoubleDecker<STATE> summarySuccDoubleDecker = 
				new DoubleDecker<STATE>(summaryPreDown, summarySucc);
			DoubleDecker<STATE> summaryReturnPred = 
				new DoubleDecker<STATE>(summaryPred, returnPred);
//			memorizePredecessor(summarySuccDoubleDecker, summaryReturnPred, m_ReturnPredecessors);
//			memorizePredecessor(summarySuccDoubleDecker, doubleDecker, m_SummaryPredecessors);
			enqueueAndMark(summarySuccDoubleDecker);
		}
	}
	
	
	
	/**
	 * Get all states <i>down</i> such that the DoubleDecker
	 * (<i>down</i>,<i>up</i>) has been visited so far.
	 */
	private final Set<STATE> getKnownDownStates(STATE up) {
		Set<STATE> downStates = m_Marked_Up2Down.get(up).keySet();
		if (downStates == null) {
			return new HashSet<STATE>(0);
		}
		else {
			return downStates;
		}
	}
	
	public Map<STATE,Map<STATE,ReachFinal>> getUp2DownMapping() {
		return Collections.unmodifiableMap(m_Marked_Up2Down);
	}
	
	
	protected final void traverseDoubleDeckerGraph() throws OperationCanceledException {
		Collection<STATE> initialStates = getInitialStates();
		for (STATE state : initialStates) {
			DoubleDecker<STATE> initialDoubleDecker = 
				new DoubleDecker<STATE>(m_TraversedNwa.getEmptyStackState(), state);
			enqueueAndMark(initialDoubleDecker);
		}
		
		while(!m_Worklist.isEmpty()) {
			DoubleDecker<STATE> doubleDecker = m_Worklist.remove(0);
			
			Iterable<STATE> internalSuccs = 
					visitAndGetInternalSuccessors(doubleDecker);
			for (STATE succ : internalSuccs) {
				DoubleDecker<STATE> succDoubleDecker = 
						new DoubleDecker<STATE>(doubleDecker.getDown(), succ);
//				memorizePredecessor(succDoubleDecker, doubleDecker, m_InternalPredecessors);
				enqueueAndMark(succDoubleDecker);
			}
			Iterable<STATE> callSuccs = 
				visitAndGetCallSuccessors(doubleDecker);
			for (STATE succ : callSuccs) {
				DoubleDecker<STATE> succDoubleDecker = 
						new DoubleDecker<STATE>(doubleDecker.getUp(), succ);
//				memorizePredecessor(succDoubleDecker, doubleDecker, m_CallPredecessors);
				enqueueAndMark(succDoubleDecker);
			}
			Iterable<STATE> returnSuccs = 
				visitAndGetReturnSuccessors(doubleDecker);
			for (STATE succ : returnSuccs) {
				addSummary(doubleDecker.getDown(), succ, doubleDecker.getUp());
				for (STATE resLinPredCallerState : 
					getKnownDownStates(doubleDecker.getDown())) {
					DoubleDecker<STATE> succDoubleDecker = 
							new DoubleDecker<STATE>(resLinPredCallerState, succ);
//					memorizePredecessor(succDoubleDecker, doubleDecker, m_ReturnPredecessors);
					enqueueAndMark(succDoubleDecker);
				}
			}
			
			if (m_CallReturnSummary.containsKey(doubleDecker.getUp())) {
				Map<STATE,STATE> summarySucc2returnPred = 
					m_CallReturnSummary.get(doubleDecker.getUp());
				for (STATE summarySucc : summarySucc2returnPred.keySet()) {
					STATE returnPred = summarySucc2returnPred.get(summarySucc);
					DoubleDecker<STATE> summarySuccDoubleDecker = 
						new DoubleDecker<STATE>(doubleDecker.getDown(), summarySucc);
					DoubleDecker<STATE> shortcutReturnPred = 
						new DoubleDecker<STATE>(doubleDecker.getUp(), returnPred);
//					memorizePredecessor(summarySuccDoubleDecker, shortcutReturnPred, m_ReturnPredecessors);
//					memorizePredecessor(summarySuccDoubleDecker, doubleDecker, m_SummaryPredecessors);
					enqueueAndMark(summarySuccDoubleDecker);
				}
			}
			if (!UltimateServices.getInstance().continueProcessing()) {
				throw new OperationCanceledException();
			}
			
			
		}
		s_Logger.info("Before removal of dead ends " + m_TraversedNwa.sizeInformation());
		if (m_RemoveDeadEnds && m_RemoveNonLiveStates) {
			throw new IllegalArgumentException("RemoveDeadEnds and RemoveNonLiveStates is set");
		}
		
		m_DeadEnds = computeDeadEnds();
		
//		Set<DoubleDecker<STATE>> oldMethod = removedDoubleDeckersOldMethod();
//		Set<DoubleDecker<STATE>> newMethod = removedDoubleDeckersViaIterator();
//		assert oldMethod.containsAll(newMethod);
//		assert newMethod.containsAll(oldMethod);



		if (m_RemoveDeadEnds) {
//			new TestFileWriter(m_TraversedNwa, "TheAutomaotn", TestFileWriter.Labeling.TOSTRING);
			removeDeadEnds();
			if (m_TraversedNwa.getInitialStates().isEmpty()) {
				assert m_TraversedNwa.getStates().isEmpty();
			}
			s_Logger.info("After removal of dead ends " + m_TraversedNwa.sizeInformation());

		}
		if (m_RemoveNonLiveStates) {
//			s_Logger.warn("Minimize before non-live removal: " + 
//		((NestedWordAutomaton<LETTER,STATE>) (new MinimizeDfa<LETTER, STATE>(m_TraversedNwa)).getResult()).sizeInformation());
			removeNonLiveStates();
//			s_Logger.warn("Minimize after non-live removal: " + 
//		((NestedWordAutomaton<LETTER,STATE>) (new MinimizeDfa<LETTER, STATE>(m_TraversedNwa)).getResult()).sizeInformation());
			if (m_TraversedNwa.getInitialStates().isEmpty()) {
				assert m_TraversedNwa.getStates().isEmpty();
//				m_TraversedNwa = getTotalizedEmptyAutomaton();
			}
			s_Logger.info("After removal of nonLiveStates " + m_TraversedNwa.sizeInformation());
		}
	}
	
//	protected NestedWordAutomaton<LETTER,STATE> getTotalizedEmptyAutomaton() {
//		NestedWordAutomaton<LETTER,STATE> emptyAutomaton = new NestedWordAutomaton<LETTER,STATE>(
//				m_TraversedNwa.getInternalAlphabet(), 
//				m_TraversedNwa.getCallAlphabet(), 
//				m_TraversedNwa.getReturnAlphabet(), 
//				m_TraversedNwa.getStateFactory());
//		STATE sinkState = emptyAutomaton.getStateFactory().createSinkStateContent();
//		emptyAutomaton.addState(true, false, sinkState);
//		
//		for (STATE state : emptyAutomaton.getStates()) {
//			for (LETTER letter : emptyAutomaton.getInternalAlphabet()) {				
//				if (emptyAutomaton.succInternal(state,letter).isEmpty()) {
//					emptyAutomaton.addInternalTransition(state, letter, sinkState);
//				}
//			}
//			for (LETTER letter : emptyAutomaton.getCallAlphabet()) {				
//				if (emptyAutomaton.succCall(state,letter).isEmpty()) {
//					emptyAutomaton.addCallTransition(state, letter, sinkState);
//				}
//			}
//			for (LETTER symbol : emptyAutomaton.getReturnAlphabet()) {
//				for (STATE hier : emptyAutomaton.getStates()) {
//					if (emptyAutomaton.succReturn(state,hier,symbol).isEmpty()) {
//						emptyAutomaton.addReturnTransition(state, hier, symbol, sinkState);
//					}
//				}
//			}
//		}
//
//		return emptyAutomaton;
//	}

	
	/**
	 * @return initial states of automaton
	 */
	protected abstract Collection<STATE> getInitialStates();

	/**
	 * @return internal successors of doubleDeckers up state
	 */
	protected abstract Collection<STATE> visitAndGetInternalSuccessors(
			DoubleDecker<STATE> doubleDecker);

	/**
	 * @return call successors of doubleDeckers up state
	 */
	protected abstract Collection<STATE> visitAndGetCallSuccessors(
			DoubleDecker<STATE> doubleDecker);

	/**
	 * @return return successors of doubleDeckers up state
	 */
	protected abstract Collection<STATE> visitAndGetReturnSuccessors(
			DoubleDecker<STATE> doubleDecker);

	
	


	private void enqueueInternalPred(STATE up, Collection<STATE> downStates, 
												DoubleDeckerWorkList worklist) {
		for (IncomingInternalTransition<LETTER, STATE> inTrans : 
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).internalPredecessors(up)) {
			STATE predUp = inTrans.getPred();
			for (STATE down : downStates) {
				ReachFinal doubleDeckerReach = m_Marked_Up2Down.get(predUp).get(down);
				if (doubleDeckerReach == ReachFinal.UNKNOWN) {
//					assert (doubleDeckersThatCanReachFinal.contains(new DoubleDecker<STATE>(down, predUp))) : "deadEndRemovalFailed";
					worklist.add(predUp, down);
				} else {
					assert doubleDeckerReach == null || doubleDeckerReach == ReachFinal.AT_LEAST_ONCE;
				}
			}
		}
	}
	
	private void enqueueCallPred(STATE up, Collection<STATE> downStates, 
												DoubleDeckerWorkList worklist) {
		// we for call transitions we may use all of predecessors
		// down states (use only when considering only non ret ancestors!)
		for (IncomingCallTransition<LETTER, STATE> inTrans : 
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).callPredecessors(up)) {
			STATE predUp = inTrans.getPred();
			for (STATE predDown : m_Marked_Up2Down.get(predUp).keySet()) {
				ReachFinal doubleDeckerReach = m_Marked_Up2Down.get(predUp).get(predDown);
				if (doubleDeckerReach == ReachFinal.UNKNOWN) {
//					assert (doubleDeckersThatCanReachFinal.contains(new DoubleDecker<STATE>(predDown, predUp))) : "deadEndRemovalFailed";
					worklist.add(predUp, predDown);
				}
				else {
					assert doubleDeckerReach == null || doubleDeckerReach == ReachFinal.AT_LEAST_ONCE;
				}
			}
		}
	}
	
	private void enqueueReturnPred(STATE up, Collection<STATE> downStates, 
										DoubleDeckerWorkList summaryWorklist, 
										DoubleDeckerWorkList linPredworklist) {
		for (IncomingReturnTransition<LETTER, STATE> inTrans : 
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).returnPredecessors(up)) {
			STATE hier = inTrans.getHierPred();
			// We have to check if there is some double decker (hier,down) with
			// down∈downStates. Only in that case we may add (lin,hier) to the
			// worklist (done after this while loop)
			boolean hierIsUpOfSomePredDoubleDecker = false;
			for (STATE down : downStates) {
				ReachFinal doubleDeckerReach = m_Marked_Up2Down.get(hier).get(down);
				if (doubleDeckerReach != null) {
					hierIsUpOfSomePredDoubleDecker = true;
					if (doubleDeckerReach == ReachFinal.UNKNOWN) {
//						assert (doubleDeckersThatCanReachFinal.contains(new DoubleDecker<STATE>(down, hier))) : "deadEndRemovalFailed";
						summaryWorklist.add(hier, down);
					} else {
						assert doubleDeckerReach == ReachFinal.AT_LEAST_ONCE;
					}
				}
			}
			STATE linPred = inTrans.getLinPred();
			if (hierIsUpOfSomePredDoubleDecker) {
				ReachFinal doubleDeckerReach = m_Marked_Up2Down.get(linPred).get(hier);
				if (doubleDeckerReach == ReachFinal.UNKNOWN) {
//					assert (doubleDeckersThatCanReachFinal.contains(new DoubleDecker<STATE>(hier, linPred))) : "deadEndRemovalFailed";
					linPredworklist.add(linPred, hier);
				} else {
					assert doubleDeckerReach == ReachFinal.AT_LEAST_ONCE;
				}
			}
		}
	}
	
	
	
	private final Set<STATE> computeDeadEnds() {
		// Set used to compute the states that can never reach the final state
		// initialized with all states and narrowed by the algorithm
		Set<STATE> statesNeverReachFinal = new HashSet<STATE>(m_TraversedNwa.getStates());
		
		{
			DoubleDeckerWorkList nonRetAncest = new DoubleDeckerWorkList();

			DoubleDeckerWorkList allAncest = new DoubleDeckerWorkList();
			
			// compute return ancestors in two steps
			
			// step one: consider only hierarchical predecessors of return 
			// transitions. Reason: We want to compute all reachable double 
			// deckers. Neglecting linPreds of return transitions all double
			// deckers (up,down) of an up state are reachable.
			for (STATE state : m_TraversedNwa.getFinalStates()) {
				Map<STATE, ReachFinal> down2reachFinal = m_Marked_Up2Down.get(state);
				if (down2reachFinal == null) {
					s_Logger.debug("Unreachable final state: " + state);
				} else {
					for (STATE down : m_Marked_Up2Down.get(state).keySet()) {
						nonRetAncest.add(state, down);
					}
				}
			}
			while (!nonRetAncest.isEmpty()) {
				Map<STATE, Set<STATE>> up2downs = nonRetAncest.removeUpAndItsDowns();
				assert up2downs.size() == 1;
				STATE up = up2downs.keySet().iterator().next();
				statesNeverReachFinal.remove(up);
				Set<STATE> downs = up2downs.get(up);
				//down states such that final reachability of (up,down) was new
				//information (and has to be propagated to predecessors.
				List<STATE> updatedDowns = new ArrayList<STATE>();
				for (STATE down : downs) {
					if (m_Marked_Up2Down.get(up).get(down) == ReachFinal.UNKNOWN) {
						updatedDowns.add(down); 
					} else {
						assert m_Marked_Up2Down.get(up).get(down) == ReachFinal.AT_LEAST_ONCE;
					}
//					assert (doubleDeckersThatCanReachFinal.contains(new DoubleDecker<STATE>(down, up))) : "deadEndRemovalFailed";
					m_Marked_Up2Down.get(up).put(down, ReachFinal.AT_LEAST_ONCE);
				}
				
				if (!updatedDowns.isEmpty()) {
					enqueueInternalPred(up, updatedDowns, nonRetAncest);

					enqueueCallPred(up, updatedDowns, nonRetAncest);
					enqueueReturnPred(up, updatedDowns, nonRetAncest, allAncest);
				}
			}
			
			//step two
			while (!allAncest.isEmpty()) {
				Map<STATE, Set<STATE>> up2downs = allAncest.removeUpAndItsDowns();
				assert up2downs.size() == 1;
				STATE up = up2downs.keySet().iterator().next();
				statesNeverReachFinal.remove(up);
				Set<STATE> downs = up2downs.get(up);
				//down states such that final reachability of (up,down) was new
				//information (and has to be propagated to predecessors.
				List<STATE> updatedDowns = new ArrayList<STATE>();
				for (STATE down : downs) {
					if (m_Marked_Up2Down.get(up).get(down) == ReachFinal.UNKNOWN) {
						updatedDowns.add(down); 
					}
//					assert (doubleDeckersThatCanReachFinal.contains(new DoubleDecker<STATE>(down, up))) : "deadEndRemovalFailed";
					m_Marked_Up2Down.get(up).put(down, ReachFinal.AT_LEAST_ONCE);
				}
				if (!updatedDowns.isEmpty()) {
					enqueueInternalPred(up, updatedDowns, allAncest);
					// we may omit call transitions - state are already
					// considered as hier preds of returns.
					enqueueReturnPred(up, updatedDowns, allAncest, allAncest);
				}
			}
		}
		return statesNeverReachFinal;
	}
	
	
//	private final Set<STATE> computeStatesThatCanNotReachFinal() {
//		
////		// Set used to compute the states that can never reach the final state
////		// initialized with all states and narrowed by the algorithm
////		Set<STATE> statesNeverReachFinal = new HashSet<STATE>(m_TraversedNwa.getStates());
////
////		{
////			Set<DoubleDecker<STATE>> nonReturnAncestors = new HashSet<DoubleDecker<STATE>>();
////		Set<DoubleDecker<STATE>> acceptingDoubleDeckers = new HashSet<DoubleDecker<STATE>>();
////		for (STATE finalState : m_TraversedNwa.getFinalStates()) {
////			Set<STATE> finalsDownStates = m_Marked_Up2Down.get(finalState).keySet();
////			for (STATE downStatesOfFinal : finalsDownStates) {
////				DoubleDecker<STATE> summary =	new DoubleDecker<STATE>(downStatesOfFinal, finalState);
////				acceptingDoubleDeckers.add(summary);
////			}
////		}
////		
////		LinkedList<DoubleDecker<STATE>> ancestorSearchWorklist;
////		
////		//Computation of nonReturnAncestors
////		ancestorSearchWorklist = new LinkedList<DoubleDecker<STATE>>();
////		ancestorSearchWorklist.addAll(acceptingDoubleDeckers);
////		nonReturnAncestors.addAll(acceptingDoubleDeckers);
////		while (!ancestorSearchWorklist.isEmpty()) {
////			DoubleDecker<STATE> doubleDecker= ancestorSearchWorklist.removeFirst();
////			statesNeverReachFinal.remove(doubleDecker.getUp());
////			ArrayList<Set<DoubleDecker<STATE>>> predSets = new ArrayList<Set<DoubleDecker<STATE>>>(3);
////			predSets.add(m_InternalPredecessors.get(doubleDecker));
////			predSets.add(m_SummaryPredecessors.get(doubleDecker));
////			predSets.add(m_CallPredecessors.get(doubleDecker));
////			for (Set<DoubleDecker<STATE>> preds : predSets) {
////				if (preds == null) {
////					//assert m_TraversedNwa.getInitial().contains(doubleDecker.getUp());
////				}
////				else {
////					for (DoubleDecker<STATE> pred : preds) {
////						if (!nonReturnAncestors.contains(pred)) {
////							nonReturnAncestors.add(pred);
////							ancestorSearchWorklist.add(pred);
////						}
////					}
////				}
////			}
////		}
////		
////		//add Return Ancestors
////		ancestorSearchWorklist = new LinkedList<DoubleDecker<STATE>>();
////		ancestorSearchWorklist.addAll(nonReturnAncestors);
////		while (!ancestorSearchWorklist.isEmpty()) {
////			DoubleDecker<STATE> doubleDecker= ancestorSearchWorklist.removeFirst();
////			statesNeverReachFinal.remove(doubleDecker.getUp());
////			ArrayList<Set<DoubleDecker<STATE>>> predSets = new ArrayList<Set<DoubleDecker<STATE>>>(3);
////			predSets.add(m_InternalPredecessors.get(doubleDecker));
////			predSets.add(m_SummaryPredecessors.get(doubleDecker));
////			predSets.add(m_ReturnPredecessors.get(doubleDecker));
////			for (Set<DoubleDecker<STATE>> preds : predSets) {
////				if (preds == null) {
////					//assert m_TraversedNwa.getInitial().contains(doubleDecker.getUp());
////				}
////				else {
////					for (DoubleDecker<STATE> pred : preds) {
////						if (!nonReturnAncestors.contains(pred)) {
////							nonReturnAncestors.add(pred);
////							ancestorSearchWorklist.add(pred);
////						}
////					}
////				}
////			}
////		}
////
////		// DoubleDeckers that have been visited in this search which starts from
////		// final states
////		doubleDeckersThatCanReachFinal = nonReturnAncestors;
////		doubleDeckersThatCanReachFinal.addAll(acceptingDoubleDeckers);
////	}
//		
//		
//		
//		
//		Set<STATE> statesNeverReachFin = computeStatesThatCanNotReachFinalNewVersion();
////		s_Logger.error("STATEs " + m_TraversedNwa.getStates().size());
//////		new TestFileWriter(m_TraversedNwa, "TheAutomaotn", TestFileWriter.Labeling.TOSTRING, "test");
////		assert statesNeverReachFinal.containsAll(statesNeverReachFin) : "deadEndRemovalFailed";
////		assert statesNeverReachFin.containsAll(statesNeverReachFinal) : "deadEndRemovalFailed";
////		
////		for (DoubleDecker<STATE> dd : doubleDeckersThatCanReachFinal) {
////			STATE up = dd.getUp();
////			STATE down = dd.getDown();
////			assert m_Marked_Up2Down.get(up).get(down) == ReachFinal.AT_LEAST_ONCE : "deadEndRemovalFailed";
////		}
////		for (STATE up : m_Marked_Up2Down.keySet()) {
////			for (STATE down : m_Marked_Up2Down.get(up).keySet()) {
////				if (m_Marked_Up2Down.get(up).get(down) == ReachFinal.AT_LEAST_ONCE && down != m_TraversedNwa.getEmptyStackState()) {
////					assert (doubleDeckersThatCanReachFinal.contains(new DoubleDecker<STATE>(down, up))) : "deadEndRemovalFailed";
////				}
////			}
////		}
//		
//		return statesNeverReachFin;
//	}
	
	
	
	/**
	 * Remove in the resulting automaton all states that can not reach a final
	 * state.
	 * @param computeRemovedDoubleDeckersAndCallSuccessors compute the set of 
	 * all DoubleDeckers which occurred in the build automaton but are not
	 * reachable after the removal 
	 * @return true iff at least one state was removed.
	 */
	public final boolean removeDeadEnds() {
		long startTime = System.currentTimeMillis();
		
		//some states are not removed but loose inital property
		Set<STATE> statesThatShouldNotBeInitialAnyMore = new HashSet<STATE>();
		for (STATE state : m_TraversedNwa.getInitialStates()) {
			if (m_DeadEnds.contains(state)) {
				continue;
			}
			if (m_Marked_Up2Down.get(state).get(m_TraversedNwa.getEmptyStackState()) == ReachFinal.AT_LEAST_ONCE) {
				continue;
			} else {
				assert m_Marked_Up2Down.get(state).get(m_TraversedNwa.getEmptyStackState()) == ReachFinal.UNKNOWN;
			}
			statesThatShouldNotBeInitialAnyMore.add(state);
		}
		for (STATE state : statesThatShouldNotBeInitialAnyMore) {
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).makeStateNonIntial(state);
			s_Logger.warn("The following state is not final any more: " +state);
		}
		
		for (STATE state : m_DeadEnds) {
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).removeState(state);
		}
		
		boolean atLeastOneStateRemoved = !m_DeadEnds.isEmpty();
		m_DeadEnds = null;
		m_DeadEndRemovalTime += (System.currentTimeMillis() - startTime);
		s_Logger.info("After removal of dead ends " + m_TraversedNwa.sizeInformation());
		return atLeastOneStateRemoved;
	}
	

//	/**
//	 * Announce removal of all DoubleDeckers (<i>down</i>,<i>up</i>) such that
//	 * <i>down</i> or <i>up</i> is contained in statesGoingToBeRemoved.
//	 */
//	// _before_ because on removal we want to be able to access all states
//	// of the automaton
//	private void announceRemovalOfDoubleDeckers(Set<STATE> statesGoingToBeRemoved) {
//		m_CallSuccOfRemovedDown = new HashMap<STATE,STATE>();		
//
//		/**
//		 * DoubleDeckers that have been constructed but do not occur in any
//		 * accepting run of the automaton.
//		 */
//		for (STATE up : m_Marked_Up2Down.keySet()) {
//			for (STATE down : m_Marked_Up2Down.get(up).keySet()) {
//				if (m_Marked_Up2Down.get(up).get(down) == ReachFinal.UNKNOWN) {
//					
//					Set<STATE> downStates = m_RemovedDoubleDeckers.get(up);
//					if (downStates == null) {
//						downStates = new HashSet<STATE>();
//						m_RemovedDoubleDeckers.put(up, downStates);
//					}
//					downStates.add(down);
//					
//					Set<STATE> downCallSuccs = computeState2CallSuccs(down);
//					if (downCallSuccs.size() > 1) {
//						throw new UnsupportedOperationException("If state has" +
//								" several outgoing call transitions Hoare annotation might be incorrect.");
//					} else if (downCallSuccs.size() == 1){
//						STATE callSucc = downCallSuccs.iterator().next();
//						m_CallSuccOfRemovedDown.put(down, callSucc);
//					} else {
//						assert downCallSuccs.isEmpty();
//					}
//				}
//			}
//		}
//	}
	
	
	
	/**
	 * Compute call successors for a given set of states.
	 */
	private Set<STATE> computeState2CallSuccs(STATE state) {
		Set<STATE> callSuccs = new HashSet<STATE>();
		if (state != m_TraversedNwa.getEmptyStackState()) {
			for (LETTER letter : m_TraversedNwa.lettersCall(state)) {
				for (STATE succ : m_TraversedNwa.succCall(state, letter)) {
					callSuccs.add(succ);
				}
			}
		}
		return callSuccs;
	}
	
	
	


	
	
	/**
	 * Return true iff state has successors
	 */
	private boolean hasSuccessors(STATE state) {
		for (LETTER symbol : m_TraversedNwa.lettersInternal(state)) {
			if (m_TraversedNwa.succInternal(state, symbol).iterator().hasNext()) {
				return true;
			}
		}
		for (LETTER symbol : m_TraversedNwa.lettersCall(state)) {
			if (m_TraversedNwa.succCall(state, symbol).iterator().hasNext()) {
				return true;
			}
		}
		for (LETTER symbol : m_TraversedNwa.lettersReturn(state)) {
			for (STATE hier : m_TraversedNwa.hierPred(state, symbol)) {
				if (m_TraversedNwa.succReturn(state, hier, symbol).iterator().hasNext()) {
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
		for (STATE accepting : m_TraversedNwa.getFinalStates()) {
			if (!hasSuccessors(accepting)) {
				finalStatesWithoutSuccessor.add(accepting);
			}
		}
		boolean atLeastOneStateRemoved = !finalStatesWithoutSuccessor.isEmpty();
		for (STATE finalStateWithoutSuccessor : finalStatesWithoutSuccessor) {
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).removeState(finalStateWithoutSuccessor);	
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
			if (m_DeadEnds == null) {
				m_DeadEnds = computeDeadEnds();
			}
			stateRemovedInInteration = removeDeadEnds();
			stateRemovedInInteration |= removeAcceptingStatesWithoutSuccessors();
		} while (stateRemovedInInteration);
	}



	public long getDeadEndRemovalTime() {
		return m_DeadEndRemovalTime;
	}

	private class DoubleDeckerSet {
		private Map<STATE, Set<STATE>> m_up2down = 
				new HashMap<STATE, Set<STATE>>();
		public void add(STATE up, STATE down) {
			Set<STATE> downStates = m_up2down.get(up);
			if (downStates == null) {
				downStates = new HashSet<STATE>();
				m_up2down.put(up, downStates);
			}
			downStates.add(down);
		}
		
		public void addAll(Collection<DoubleDecker<STATE>> collection) {
			for (DoubleDecker<STATE> dd : collection) {
				this.add(dd.getUp(), dd.getDown());
			}
		}
		
		public Map<STATE, Set<STATE>> getUp2DownMap() {
			return m_up2down;
		}
	}
	
	
	private class DoubleDeckerWorkList {
		private Map<STATE, Set<STATE>> m_up2down = new HashMap<STATE, Set<STATE>>();
		
		public void add(STATE up, STATE down) {
			Set<STATE> downStates = m_up2down.get(up);
			if (downStates == null) {
				downStates = new HashSet<STATE>();
				m_up2down.put(up, downStates);
			}
			downStates.add(down);
		}
		
		public void add(STATE up, Collection<STATE> downs) {
			Set<STATE> downStates = m_up2down.get(up);
			if (downStates == null) {
				downStates = new HashSet<STATE>();
				m_up2down.put(up, downStates);
			}
			downStates.addAll(downs);
		}

		
		
		
		
		public boolean isEmpty() {
			return m_up2down.isEmpty();
		}
		
		public Map<STATE, Set<STATE>> removeUpAndItsDowns () {
			STATE up = m_up2down.keySet().iterator().next();
			Map<STATE, Set<STATE>> result = new HashMap<STATE, Set<STATE>>(1);
			result.put(up, m_up2down.get(up));
			m_up2down.remove(up);
			return result;
		}
	}
	

	
	
//	@Override
//	public boolean removeStatesThatCanNotReachFinal(
//			boolean computeRemovedDoubleDeckersAndCallSuccessors) {
//		// TODO Auto-generated method stub
//		return false;
//	}

	@Override
	public Iterable<UpDownEntry<STATE>> getRemovedUpDownEntry() {
		
		return new Iterable<UpDownEntry<STATE>>() {

			@Override
			public Iterator<UpDownEntry<STATE>> iterator() {
				return new Iterator<UpDownEntry<STATE>>() {
					private Iterator<STATE> m_UpIterator;
					private STATE m_Up;
					private Iterator<STATE> m_DownIterator;
					private STATE m_Down;
					boolean m_hasNext = true;

					{
						m_UpIterator = getUp2DownMapping().keySet().iterator();
						if (m_UpIterator.hasNext()) {
							m_Up = m_UpIterator.next();
							m_DownIterator = getUp2DownMapping().get(m_Up).keySet().iterator();
						} else {
							m_hasNext = false;
						}
						computeNextElement();
						
					}
					
					private void computeNextElement() {
						m_Down = null;
						while (m_Down == null && m_hasNext) {
							if (m_DownIterator.hasNext()) {
								STATE downCandidate = m_DownIterator.next();
								ReachFinal reach = getUp2DownMapping().get(m_Up).get(downCandidate);
								if (reach == ReachFinal.UNKNOWN) {
									m_Down = downCandidate;
								} else {
									assert reach == ReachFinal.AT_LEAST_ONCE;
								}
							} else {
								if (m_UpIterator.hasNext()) {
									m_Up = m_UpIterator.next();
									m_DownIterator = getUp2DownMapping().get(m_Up).keySet().iterator();
								} else {
									m_hasNext = false;
								}
							}
							
						}
					}

					@Override
					public boolean hasNext() {
						return m_hasNext;
					}

					@Override
					public UpDownEntry<STATE> next() {
						if (!hasNext()) {
							throw new NoSuchElementException();
						}
						STATE entry;
						Set<STATE> callSuccs = computeState2CallSuccs(m_Down);
						if (callSuccs.size() > 1 ) {
							throw new UnsupportedOperationException("State has more than one call successor");
						} else if (callSuccs.size() == 1 ) {
							entry = callSuccs.iterator().next();
						} else {
							entry = null;
							assert m_Down == m_TraversedNwa.getEmptyStackState();
						}
						UpDownEntry<STATE> result  = new UpDownEntry<STATE>(m_Up, m_Down, entry);
						computeNextElement();
						return result;
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				
					
				};
				
			}
			
			/**
			 * Compute call successors for a given set of states.
			 */
			private Set<STATE> computeState2CallSuccs(STATE state) {
				Set<STATE> callSuccs = new HashSet<STATE>();
				if (state != m_TraversedNwa.getEmptyStackState()) {
					for (LETTER letter : m_TraversedNwa.lettersCall(state)) {
						for (STATE succ : m_TraversedNwa.succCall(state, letter)) {
							callSuccs.add(succ);
						}
					}
				}
				return callSuccs;
			}
			
			
		};

	}
	private Set<DoubleDecker<STATE>> removedDoubleDeckersOldMethod() {
		Set<DoubleDecker<STATE>> result = new HashSet<DoubleDecker<STATE>>();
		for (STATE up : m_Marked_Up2Down.keySet()) {
			for (STATE down : m_Marked_Up2Down.get(up).keySet()) {
				if (m_Marked_Up2Down.get(up).get(down) == ReachFinal.UNKNOWN) {
					result.add(new DoubleDecker<STATE>(down,up));
				}
			}
		}
		return result;
	}
	
	
	private Set<DoubleDecker<STATE>> removedDoubleDeckersViaIterator() {
		Set<DoubleDecker<STATE>> result = new HashSet<DoubleDecker<STATE>>();
		for (UpDownEntry<STATE> upDownEntry : getRemovedUpDownEntry()) {
			result.add(new DoubleDecker<STATE>(upDownEntry.getDown(),upDownEntry.getUp()));
		}
		return result;
	}
}
