package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

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

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.ReachableStatesAutomaton.CommonEntriesComponent;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.ReachableStatesAutomaton.Entry;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.ReachableStatesAutomaton.StateContainer;

public class ReachableStatesAutomaton<LETTER,STATE> implements INestedWordAutomaton<LETTER,STATE> {

	
	private final NestedWordAutomaton<LETTER,STATE> m_Operand;
	
	private final Collection<LETTER> m_InternalAlphabet;
	private final Collection<LETTER> m_CallAlphabet;
	private final Collection<LETTER> m_ReturnAlphabet;
	
	protected final StateFactory<STATE> m_StateFactory;
	
	private final Map<STATE,StateContainer> m_States = 
			new HashMap<STATE,StateContainer>();
	
	private final Set<STATE> m_initialStates = new HashSet<STATE>();
	
	private final DoubleDeckerWorklist doubleDeckerWorklist = new DoubleDeckerWorklist();
	
	public ReachableStatesAutomaton(NestedWordAutomaton<LETTER,STATE> operand) {
		this.m_Operand = operand;
		m_InternalAlphabet = operand.getAlphabet();
		m_CallAlphabet = operand.getCallAlphabet();
		m_ReturnAlphabet = operand.getReturnAlphabet();
		m_StateFactory = operand.getStateFactory();
	}
	
	public class DoubleDeckerWorklist {
		LinkedList<STATE> m_UpStates = new LinkedList<STATE>();
		LinkedList<STATE> m_DownStates = new LinkedList<STATE>();
		
		public void enqueue(STATE up, STATE down) {
			m_UpStates.add(up);
			m_DownStates.add(down);
		}
		
		public boolean isEmpty() {
			return m_UpStates.isEmpty();
		}
		
		public DoubleDecker<STATE> dequeue() {
			return new DoubleDecker<STATE>(
					m_DownStates.remove(0), m_UpStates.remove(0));
		}
	}
	
	public class Entry {
		final STATE m_State;
		
		public Entry(STATE state) {
			this.m_State = state;
		}
	}
	
	public class CommonEntriesComponent {
		int m_Size = 0;
		final Set<Entry> m_Entries;
		final Set<STATE> m_DownStates;
		final Set<STATE> m_ReturnOutCandidates;
		final Map<STATE,Set<STATE>> m_BorderOut;
		
		public CommonEntriesComponent(Set<Entry> entries) {
			this.m_Entries = entries;
			this.m_DownStates = new HashSet<STATE>();
			this.m_ReturnOutCandidates = new HashSet<STATE>();
			this.m_BorderOut = new HashMap<STATE,Set<STATE>>();
		}
		
		public CommonEntriesComponent(STATE state) {
			Entry entry = new Entry(state);
			this.m_Entries = new HashSet<Entry>(1);
			this.m_Entries.add(entry);
			this.m_DownStates = new HashSet<STATE>();
			this.m_ReturnOutCandidates = new HashSet<STATE>();
			this.m_BorderOut = new HashMap<STATE,Set<STATE>>();
		}
		
		public CommonEntriesComponent(CommonEntriesComponent succCEC,
				CommonEntriesComponent stateCec) {
			this.m_Entries = new HashSet<Entry>();
			this.m_Entries.addAll(succCEC.getEntries());
			this.m_Entries.addAll(stateCec.getEntries());
			this.m_DownStates = new HashSet<STATE>();
			this.m_DownStates.addAll(succCEC.getDownStates());
			this.m_DownStates.addAll(stateCec.getDownStates());
			this.m_ReturnOutCandidates = new HashSet<STATE>();
			this.m_BorderOut = new HashMap<STATE,Set<STATE>>();

		}

		public Set<Entry> getEntries() {
			return Collections.unmodifiableSet(this.m_Entries);
		}
		
		public void addReturnOutCandicate(STATE returnCandidate) {
			m_ReturnOutCandidates.add(returnCandidate);
		}
		
		public void removeReturnOutCandicate(STATE returnCandidate) {
			boolean modified = m_ReturnOutCandidates.remove(returnCandidate);
			if (!modified) {
				throw new AssertionError("state not contained");
			}
		}
		
		public Set<STATE> getReturnOutCandidates() {
			return m_ReturnOutCandidates;
		}
		
		public Set<STATE> getDownStates() {
			return Collections.unmodifiableSet(this.m_DownStates);
		}
		
		public boolean isBorderState(STATE state) {
			return m_BorderOut.containsKey(state);
		}
		
		public void removeBorderState(STATE resident) {
			Set<STATE> foreigners = m_BorderOut.remove(resident);
			if (foreigners == null) {
				throw new AssertionError("state not contained");
			}
		}
		
		public Set<STATE> getForeigners(STATE resident) {
			return m_BorderOut.get(resident);
		}
		
		public void addBorderCrossing(STATE resident, STATE foreigner) {
			Set<STATE> foreigners = m_BorderOut.get(resident);
			if (foreigners == null) {
				foreigners = new HashSet<STATE>();
				m_BorderOut.put(resident, foreigners);
			}
			foreigners.add(foreigner);
		}
		
		
		public void addDownState(STATE down) {
			m_DownStates.add(down);
		}
	}
	
	private void addState(STATE state) {
		
	}
	
	private void addInitialStates(Iterable<STATE> initialStates) {
		for (STATE state : initialStates) {
			this.m_initialStates.add(state);
			CommonEntriesComponent cec = new CommonEntriesComponent(state);
			StateContainer sc = new StateContainer(state, cec);
			m_States.put(state, sc);
		}
		
	}
	
	private StateContainer addToCecOrConstructNewCEC(STATE state, CommonEntriesComponent cec) {
		StateContainer sc = m_States.get(state);
		if (sc == null) {
			sc = new StateContainer(state, cec);
			m_States.put(state, sc);
		} else {
			if (sc.getCommonEntriesComponent() != cec) {
				updateCECs(state, cec, sc.getCommonEntriesComponent());
			}
		}
		return sc;
	}
	
	private StateContainer getStateContainerForEntry(STATE callSucc, STATE callPred) {
		StateContainer sc = m_States.get(callSucc);
		final CommonEntriesComponent resultCec;
		if (sc == null) {
			resultCec = new CommonEntriesComponent(callSucc);
			sc = new StateContainer(callSucc, resultCec);
			m_States.put(callSucc, sc);
		} else {
			if (true) { //cec contains entry TODO
				resultCec = sc.getCommonEntriesComponent();
			} else {
				CommonEntriesComponent oldCec = sc.getCommonEntriesComponent();
				Set<Entry> entries = oldCec.getEntries();
				Set<Entry> newEntries = new HashSet<Entry>(entries);
				newEntries.add(new Entry(callSucc));
				resultCec = new CommonEntriesComponent(newEntries);
				updateCECs(callSucc, resultCec, oldCec);
			}
		}
		resultCec.addDownState(callPred);
		return sc;
	}
	
	private boolean stateCanNotHaveOutgoingCall(STATE state) {
		return false;
	}
	
	
	
	
	private void updateCECs(STATE splitStart, CommonEntriesComponent newCec, CommonEntriesComponent oldCec, Set<STATE> newDownStates) {
		Set<STATE> visited = new HashSet<STATE>();
		List<STATE> worklist = new LinkedList<STATE>();
		worklist.add(splitStart);
		while (!worklist.isEmpty()) {
			STATE state = worklist.get(0);
			visited.add(state);
			if (oldCec.getReturnOutCandidates().contains(state)) {
				newCec.addReturnOutCandicate(state);
				oldCec.removeReturnOutCandicate(state);
				for(STATE down : newDownStates) {
					doubleDeckerWorklist.enqueue(state, down);
				}
			}
			if (oldCec.isBorderState(state)) {
				Set<STATE> foreigners = oldCec.getForeigners(state);
				newCec.m_BorderOut.put(state, foreigners);
				oldCec.m_BorderOut.remove(state);
			}
			StateContainer stateSc = m_States.get(state);
			stateSc.setCommonEntriesComponent(newCec);
			oldCec.m_Size--;
			newCec.m_Size++;
			
			for (OutgoingInternalTransition<LETTER, STATE> trans : stateSc.internalSuccessors()) {
				STATE succ = trans.getSucc();
				if (!visited.contains(succ)) {
					worklist.add(succ);
				}
			}
			for (STATE succ : summarySuccs(state)) {
				if (!visited.contains(succ)) {
					worklist.add(succ);
				}
			}
		}
		
		if (oldCec.m_Size != 0) {
			assert (oldCec.m_Size > 0);
			// we have to check all states of the newCec if they have an
			// incoming transition from the oldCec and set m_BorderOut of
			// oldCec accordingly
			for (STATE state : visited) {
				StateContainer sc = m_States.get(state);
				for (IncomingInternalTransition<LETTER, STATE> inTrans : sc.internalPredecessors()) {
					STATE pred = inTrans.getPred();
					StateContainer predSc = m_States.get(pred);
					if (predSc.getCommonEntriesComponent() == oldCec) {
						oldCec.addBorderCrossing(pred, state);
					}
				}
				for (IncomingReturnTransition<LETTER, STATE> inTrans : sc.returnPredecessors()) {
					STATE hierPred = inTrans.getHierPred();
					StateContainer predSc = m_States.get(hierPred);
					if (predSc.getCommonEntriesComponent() == oldCec) {
						oldCec.addBorderCrossing(hierPred, state);
					}
				}
			}
		}
	}
	
	private Set<STATE> summarySuccs(STATE state) {
		return null;
	}
	
	private void buildAllStates() {
		List<StateContainer> worklist = new LinkedList<StateContainer>();
		Set<STATE> visited = new HashSet<STATE>();
		
		for (STATE state : this.getInitialStates()) {
			worklist.add(m_States.get(state));
		}
		
		while (!worklist.isEmpty()) {
			StateContainer sc = worklist.remove(0);
			STATE state = sc.getState();
			visited.add(state);
			CommonEntriesComponent stateCec = sc.getCommonEntriesComponent(); 
			for (OutgoingInternalTransition<LETTER, STATE> trans : m_Operand.internalSuccessors(state)) {
				STATE succ = trans.getSucc();
				StateContainer succSC = m_States.get(state);
				if (succSC == null) {
					succSC = new StateContainer(succ, stateCec);
					m_States.put(succ, succSC);
				} else {
					CommonEntriesComponent succCEC = succSC.getCommonEntriesComponent();
					if (stateCec != succCEC) {
						succCEC = computeCec(state, stateCec, succ, succCEC);
						
					}
				}
				sc.addInternalOutgoing(trans);
				succSC.addInternalIncoming(new IncomingInternalTransition<LETTER, STATE>(state, trans.getLetter()));
				if (!visited.contains(succ)) {
					worklist.add(succSC);
				}
			}
			
			for (OutgoingCallTransition<LETTER, STATE> trans : m_Operand.callSuccessors(state)) {
				STATE succ = trans.getSucc();
				StateContainer succSC = getStateContainerForEntry(succ, state);
				CommonEntriesComponent succCEC = succSC.getCommonEntriesComponent();
				sc.addCallOutgoing(trans);
				succSC.addCallIncoming(new IncomingCallTransition<LETTER, STATE>(state, trans.getLetter()));
				addNewlyEnabledReturnTransitions(succCEC, state);
				if (!visited.contains(succ)) {
					worklist.add(succSC);
				}
			}

			StateContainer stateSc = m_States.get(state);
			CommonEntriesComponent stateCEC = stateSc.getCommonEntriesComponent();
			//TODO: need copy to avoid concurModExcpetion
			for (STATE down : stateCEC.getDownStates()) {
				StateContainer downSC = m_States.get(down);
				CommonEntriesComponent downCec = downSC.getCommonEntriesComponent(); 
				for (OutgoingReturnTransition<LETTER, STATE> trans : m_Operand.returnSuccessorsGivenHier(state, down)) {
					STATE succ = trans.getSucc();
					StateContainer succSC = addToCecOrConstructNewCEC(succ, downCec);
					sc.addReturnOutgoing(trans);
					succSC.addReturnIncoming(new IncomingReturnTransition<LETTER, STATE>(state, down, trans.getLetter()));
					if (!visited.contains(succ)) {
						worklist.add(succSC);
					}
				}
				

			}


		}
		
	}
	

	private void addNewlyEnabledReturnTransitions(
			CommonEntriesComponent cec, STATE state) {
		List<CommonEntriesComponent> worklist = new LinkedList<CommonEntriesComponent>(); 
		Set<CommonEntriesComponent> visitedCECs = new HashSet<CommonEntriesComponent>();
		
		
	}

	private CommonEntriesComponent computeCec(STATE state, CommonEntriesComponent stateCec,
			STATE succ, CommonEntriesComponent succCEC) {
		if (succCEC == null) {
			return stateCec;
		} else if (succCEC == stateCec) {
			return stateCec;
		} else {
			CommonEntriesComponent result = new CommonEntriesComponent(succCEC, stateCec);
			Set<STATE> newDownStates = stateCec.getDownStates();
			newDownStates.removeAll(succCEC.getDownStates());
			updateCECs(succ, result, stateCec, newDownStates);
			stateCec.addBorderCrossing(state, succ);
			return result;
		}
	}

	@Override
	public IRun<LETTER, STATE> acceptingRun() throws OperationCanceledException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean accepts(Word<LETTER> word) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public Collection<LETTER> getAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> getInternalAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> getCallAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> getReturnAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> getStates() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> getInitialStates() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> getFinalStates() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isInitial(STATE state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isFinal(STATE state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void addState(boolean isInitial, boolean isFinal, STATE state) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void removeState(STATE state) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public STATE getEmptyStackState() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersInternal(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersCall(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersReturn(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersInternalIncoming(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersCallIncoming(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersReturnIncoming(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersReturnSummary(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<STATE> succInternal(STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<STATE> succCall(STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<STATE> hierPred(STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<STATE> predInternal(STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<STATE> predCall(STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<STATE> predReturnLin(STATE state, LETTER letter, STATE hier) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<STATE> predReturnHier(STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void addInternalTransition(STATE pred, LETTER letter, STATE succ) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void addCallTransition(STATE pred, LETTER letter, STATE succ) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void addReturnTransition(STATE pred, STATE hier, LETTER letter,
			STATE succ) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean finalIsTrap() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isDeterministic() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isTotal() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> getSummaryReturnTransitions(
			LETTER letter, STATE hier) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> getIncomingReturnTransitions(
			LETTER letter, STATE hier) {
		// TODO Auto-generated method stub
		return null;
	}
	
	
	
	
	
	
	
	/**
	 * Contains STATES and information of transitions.
	 *
	 * @param <LETTER>
	 * @param <STATE>
	 */
	public class StateContainer {
		private final STATE m_State;
		
		private CommonEntriesComponent cec;
		/**
		 * Set of internal transitions PREs x LETTERs x SUCCs stored as map
		 * PREs -> LETTERs -> SUCCs
		 * The keySet of this map is used to store the set of states of this
		 * automaton.
		 */
		private Map<LETTER,Set<STATE>> m_InternalOut;
		
		/**
		 * Set of internal transitions PREs x LETTERs x SUCCs stored as map
		 * SUCCs -> LETTERs -> PREs
		 */
		private Map<LETTER,Set<STATE>> m_InternalIn =
				new HashMap<LETTER,Set<STATE>>();
		
		/**
		 * Set of call transitions PREs x LETTERs x SUCCs stored as map
		 * PREs -> LETTERs -> SUCCs
		 */
		private Map<LETTER,Set<STATE>> m_CallOut =
				new HashMap<LETTER,Set<STATE>>();
		
		/**
		 * Set of call transitions PREs x LETTERs x SUCCs stored as map
		 * SUCCs -> LETTERs -> PREs
		 */
		private Map<LETTER,Set<STATE>> m_CallIn =
				new HashMap<LETTER,Set<STATE>>();
		
		/**
		 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as 
		 * map LinPREs -> LETTERs -> HierPREs -> SUCCs
		 * 
		 */
		private Map<LETTER,Map<STATE,Set<STATE>>> m_ReturnOut =
				new HashMap<LETTER,Map<STATE,Set<STATE>>>();
		
		/**
		 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as 
		 * map HierPREs -> LETTERs -> LinPREs -> SUCCs
		 * 
		 */
		private Map<STATE,Map<LETTER,Map<STATE,Set<STATE>>>> m_ReturnSummary =
				new HashMap<STATE,Map<LETTER,Map<STATE,Set<STATE>>>>();
		
		/**
		 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as 
		 * map SUCCs -> LETTERs -> HierPREs -> LinPREs
		 * 
		 */
		private Map<LETTER,Map<STATE,Set<STATE>>> m_ReturnIn =
				new HashMap<LETTER,Map<STATE,Set<STATE>>>();

		private Set<LETTER> m_EmptySetOfLetters = new HashSet<LETTER>(0);

		private Collection<STATE> m_EmptySetOfStates = new HashSet<STATE>(0);
		
		public StateContainer(STATE state, CommonEntriesComponent cec) {
			this.cec = cec;
			m_State = state;
		}
		
		CommonEntriesComponent getCommonEntriesComponent() {
			return cec;
		}
		
		void setCommonEntriesComponent(CommonEntriesComponent cec) {
			this.cec = cec;
		}

		
		STATE getState() {
			return m_State;
		}
		
		
		
		public void addInternalOutgoing(OutgoingInternalTransition<LETTER, STATE> internalOutgoing) {
			
		}
		
		public void addInternalIncoming(IncomingInternalTransition<LETTER, STATE> internalIncoming) {
			
		}
		
		public void addCallOutgoing(OutgoingCallTransition<LETTER, STATE> callOutgoing) {
			
		}
		
		public void addCallIncoming(IncomingCallTransition<LETTER, STATE> callIncoming) {
			
		}
		
		public void addReturnOutgoing(OutgoingReturnTransition<LETTER, STATE> returnOutgoing) {
			
		}
		
		public void addReturnIncoming(IncomingReturnTransition<LETTER, STATE> returnIncoming) {
			
		}

		
		
		
		public Collection<LETTER> lettersInternal() {
			Map<LETTER, Set<STATE>> map = m_InternalOut;
			return map == null ? m_EmptySetOfLetters : map.keySet();
		}
		

		public Collection<LETTER> lettersInternalIncoming() {
			Map<LETTER, Set<STATE>> map = m_InternalIn;
			return map == null ? m_EmptySetOfLetters : map.keySet();
		}
		
		public Collection<LETTER> lettersCall() {
			Map<LETTER, Set<STATE>> map = m_CallOut;
			return map == null ? m_EmptySetOfLetters : map.keySet();
		}
		
		public Collection<LETTER> lettersCallIncoming() {
			Map<LETTER, Set<STATE>> map = m_CallIn;
			return map == null ? m_EmptySetOfLetters : map.keySet();
		}
		
		public Collection<LETTER> lettersReturn() {
			Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnOut;
			return map == null ? m_EmptySetOfLetters : map.keySet();
		}
		
		public Collection<LETTER> lettersReturnIncoming() {
			 Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnIn;
			return map == null ? m_EmptySetOfLetters : map.keySet();
		}
		
		
//		@Override
//		public Collection<LETTER> lettersReturnSummary(STATE state) {
//			if (!contains(state)) {
//				throw new IllegalArgumentException("State " + state + " unknown");
//			}
//			 Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnSummary.get(state);
//			return map == null ? m_EmptySetOfLetters : map.keySet();
//		}
	//	
	//	
//		@Override
//		public Collection<STATE> succInternal(STATE state, LETTER letter) {
//			assert contains(state);
//			Map<LETTER, Set<STATE>> map = m_InternalOut.get(state);
//			if (map == null) {
//				return m_EmptySetOfStates;
//			}
//			Set<STATE> result = map.get(letter);
//			return result == null ? m_EmptySetOfStates : result;
//		}
	//	
//		@Override
//		public Collection<STATE> predInternal(STATE state, LETTER letter) {
//			assert contains(state);
//			Map<LETTER, Set<STATE>> map = m_InternalIn.get(state);
//			if (map == null) {
//				return m_EmptySetOfStates;
//			}
//			Set<STATE> result = map.get(letter);
//			return result == null ? m_EmptySetOfStates : result;
//		}
	//	
//		@Override
//		public Collection<STATE> succCall(STATE state, LETTER letter) {
//			assert contains(state);
//			Map<LETTER, Set<STATE>> map = m_CallOut.get(state);
//			if (map == null) {
//				return m_EmptySetOfStates;
//			}
//			Set<STATE> result = map.get(letter);
//			return result == null ? m_EmptySetOfStates : result;
//		}
	//	
//		@Override
//		public Collection<STATE> predCall(STATE state, LETTER letter) {
//			assert contains(state);
//			Map<LETTER, Set<STATE>> map = m_CallIn.get(state);
//			if (map == null) {
//				return m_EmptySetOfStates;
//			}
//			Set<STATE> result = map.get(letter);
//			return result == null ? m_EmptySetOfStates : result;
//		}
	//	
//		@Override
//		public Collection<STATE> hierPred(STATE state, LETTER letter) {
//			assert contains(state);
//			Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnOut.get(state);
//			if (map == null) {
//				return m_EmptySetOfStates;
//			}
//			 Map<STATE, Set<STATE>> hier2succs = map.get(letter);
//			return hier2succs == null ? m_EmptySetOfStates : hier2succs.keySet();
//		}
	//	
//		@Override
//		public Collection<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
//			assert contains(state);
//			assert contains(hier);
//			Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnOut.get(state);
//			if (map == null) {
//				return m_EmptySetOfStates;
//			}
//			Map<STATE, Set<STATE>> hier2succs = map.get(letter);
//			if (hier2succs == null) {
//				return m_EmptySetOfStates;
//			}
//			Set<STATE> result = hier2succs.get(hier);
//			return result == null ? m_EmptySetOfStates : result;
//		}
	//	
//		@Override
//		public Collection<STATE> predReturnLin(STATE state, LETTER letter, STATE hier) {
//			assert contains(state);
//			assert contains(hier);
//			Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds  = m_ReturnIn.get(state);
//			if (letter2hier2preds == null) {
//				return m_EmptySetOfStates;
//			}
//			Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
//			if (hier2preds == null) {
//				return m_EmptySetOfStates;
//			}
//			Set<STATE> result = hier2preds.get(hier);
//			return result == null ? m_EmptySetOfStates : result;
//		}
	//	
//		@Override
		public Collection<STATE> predReturnHier(LETTER letter) {
			Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds  = m_ReturnIn;
			if (letter2hier2preds == null) {
				return m_EmptySetOfStates ;
			}
			Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
			if (hier2preds == null) {
				return m_EmptySetOfStates;
			}
			return hier2preds.keySet();
		}
		
//		@Override
//		public Iterable<SummaryReturnTransition<LETTER, STATE>> 
//							getSummaryReturnTransitions(LETTER letter, STATE hier) {
//			Set<SummaryReturnTransition<LETTER, STATE>> result = 
//					new HashSet<SummaryReturnTransition<LETTER, STATE>>();
//			Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succ = 
//					m_ReturnSummary.get(hier);
//			if (letter2pred2succ == null) {
//				return result;
//			}
//			Map<STATE, Set<STATE>> pred2succ = letter2pred2succ.get(letter);
//			if (pred2succ == null) {
//				return result;
//			}
//			for (STATE pred : pred2succ.keySet()) {
//				if (pred2succ.get(pred) != null) {
//					for (STATE succ : pred2succ.get(pred)) {
//					SummaryReturnTransition<LETTER, STATE> srt = 
//						new SummaryReturnTransition<LETTER, STATE>(pred, letter, succ);
//					result.add(srt);
//					}
//				}
//			}
//			return result;
//		}
	//	
	//	
//		@Override
//		public Iterable<IncomingReturnTransition<LETTER, STATE>> 
//							getIncomingReturnTransitions(LETTER letter, STATE succ) {
//			Set<IncomingReturnTransition<LETTER, STATE>> result = 
//					new HashSet<IncomingReturnTransition<LETTER, STATE>>();
//			Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = 
//					m_ReturnIn.get(succ);
//			if (letter2hier2pred == null) {
//				return result;
//			}
//			Map<STATE, Set<STATE>> hier2pred = letter2hier2pred.get(letter);
//			if (hier2pred == null) {
//				return result;
//			}
//			for (STATE hier : hier2pred.keySet()) {
//				if (hier2pred.get(hier) != null) {
//					for (STATE pred : hier2pred.get(hier)) {
//						IncomingReturnTransition<LETTER, STATE> srt = 
//						new IncomingReturnTransition<LETTER, STATE>(pred, hier, letter);
//					result.add(srt);
//					}
//				}
//			}
//			return result;
//		}
		
		
		
		public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
				final LETTER letter) {
			return new Iterable<IncomingInternalTransition<LETTER, STATE>>() {
				@Override
				public Iterator<IncomingInternalTransition<LETTER, STATE>> iterator() {
					Iterator<IncomingInternalTransition<LETTER, STATE>> iterator = 
							new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
						Iterator<STATE> m_Iterator;
						{
							Map<LETTER, Set<STATE>> letter2pred = m_InternalIn;
							if (letter2pred != null) {
								if (letter2pred.get(letter) != null) {
									m_Iterator = letter2pred.get(letter).iterator();
								} else {
									m_Iterator = null;
								}
							} else {
								m_Iterator = null;
							}
						}
	
						@Override
						public boolean hasNext() {
							return m_Iterator == null || m_Iterator.hasNext();
						}
	
						@Override
						public IncomingInternalTransition<LETTER, STATE> next() {
							if (m_Iterator == null) {
								throw new NoSuchElementException();
							} else {
								STATE pred = m_Iterator.next(); 
								return new IncomingInternalTransition<LETTER, STATE>(pred, letter);
							}
						}
	
						@Override
						public void remove() {
							throw new UnsupportedOperationException();
						}
					};
					return iterator;
				}
			};
		}
		
		
		
		public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors() {
			return new Iterable<IncomingInternalTransition<LETTER, STATE>>() {
				/**
				 * Iterates over all IncomingInternalTransition of succ.
				 * Iterates over all incoming internal letters and uses the 
				 * iterators returned by internalPredecessors(letter, succ)
				 */
				@Override
				public Iterator<IncomingInternalTransition<LETTER, STATE>> iterator() {
					Iterator<IncomingInternalTransition<LETTER, STATE>> iterator = 
							new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
						Iterator<LETTER> m_LetterIterator;
						LETTER m_CurrentLetter;
						Iterator<IncomingInternalTransition<LETTER, STATE>> m_CurrentIterator;
						{
							m_LetterIterator = lettersInternalIncoming().iterator();
							nextLetter();
						}
	
						private void nextLetter() {
							if (m_LetterIterator.hasNext()) {
								do {
									m_CurrentLetter = m_LetterIterator.next();
									m_CurrentIterator = internalPredecessors(
											m_CurrentLetter).iterator();
								} while (!m_CurrentIterator.hasNext()
										&& m_LetterIterator.hasNext());
								if (!m_CurrentIterator.hasNext()) {
									m_CurrentLetter = null;
									m_CurrentIterator = null;
								}
							} else {
								m_CurrentLetter = null;
								m_CurrentIterator = null;
							}
						}
	
						@Override
						public boolean hasNext() {
							return m_CurrentLetter != null;
						}
	
						@Override
						public IncomingInternalTransition<LETTER, STATE> next() {
							if (m_CurrentLetter == null) {
								throw new NoSuchElementException();
							} else {
								IncomingInternalTransition<LETTER, STATE> result = 
										m_CurrentIterator.next();
								if (!m_CurrentIterator.hasNext()) {
									nextLetter();
								}
								return result;
							}
						}
	
						@Override
						public void remove() {
							throw new UnsupportedOperationException();
						}
					};
					return iterator;
				}
			};
		}
		
		
		
		
		
//		public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
//				final LETTER letter, final STATE succ) {
//			return new Iterable<IncomingCallTransition<LETTER, STATE>>() {
//				@Override
//				public Iterator<IncomingCallTransition<LETTER, STATE>> iterator() {
//					Iterator<IncomingCallTransition<LETTER, STATE>> iterator = 
//							new Iterator<IncomingCallTransition<LETTER, STATE>>() {
//						Iterator<STATE> m_Iterator;
//						{
//							Map<LETTER, Set<STATE>> letter2pred = m_CallIn.get(succ);
//							if (letter2pred != null) {
//								if (letter2pred.get(letter) != null) {
//									m_Iterator = letter2pred.get(letter).iterator();
//								} else {
//									m_Iterator = null;
//								}
//							} else {
//								m_Iterator = null;
//							}
//						}
	//
//						@Override
//						public boolean hasNext() {
//							return m_Iterator == null || m_Iterator.hasNext();
//						}
	//
//						@Override
//						public IncomingCallTransition<LETTER, STATE> next() {
//							if (m_Iterator == null) {
//								throw new NoSuchElementException();
//							} else {
//								STATE pred = m_Iterator.next(); 
//								return new IncomingCallTransition<LETTER, STATE>(pred, letter);
//							}
//						}
	//
//						@Override
//						public void remove() {
//							throw new UnsupportedOperationException();
//						}
//					};
//					return iterator;
//				}
//			};
//		}
	//	
	//	
	//	
//		public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
//				final STATE succ) {
//			return new Iterable<IncomingCallTransition<LETTER, STATE>>() {
//				/**
//				 * Iterates over all IncomingCallTransition of succ.
//				 * Iterates over all incoming call letters and uses the 
//				 * iterators returned by callPredecessors(letter, succ)
//				 */
//				@Override
//				public Iterator<IncomingCallTransition<LETTER, STATE>> iterator() {
//					Iterator<IncomingCallTransition<LETTER, STATE>> iterator = 
//							new Iterator<IncomingCallTransition<LETTER, STATE>>() {
//						Iterator<LETTER> m_LetterIterator;
//						LETTER m_CurrentLetter;
//						Iterator<IncomingCallTransition<LETTER, STATE>> m_CurrentIterator;
//						{
//							m_LetterIterator = lettersCallIncoming(succ).iterator();
//							nextLetter();
//						}
	//
//						private void nextLetter() {
//							if (m_LetterIterator.hasNext()) {
//								do {
//									m_CurrentLetter = m_LetterIterator.next();
//									m_CurrentIterator = callPredecessors(
//											m_CurrentLetter, succ).iterator();
//								} while (!m_CurrentIterator.hasNext()
//										&& m_LetterIterator.hasNext());
//								if (!m_CurrentIterator.hasNext()) {
//									m_CurrentLetter = null;
//									m_CurrentIterator = null;
//								}
//							} else {
//								m_CurrentLetter = null;
//								m_CurrentIterator = null;
//							}
//						}
	//
//						@Override
//						public boolean hasNext() {
//							return m_CurrentLetter != null;
//						}
	//
//						@Override
//						public IncomingCallTransition<LETTER, STATE> next() {
//							if (m_CurrentLetter == null) {
//								throw new NoSuchElementException();
//							} else {
//								IncomingCallTransition<LETTER, STATE> result = 
//										m_CurrentIterator.next();
//								if (!m_CurrentIterator.hasNext()) {
//									nextLetter();
//								}
//								return result;
//							}
//						}
	//
//						@Override
//						public void remove() {
//							throw new UnsupportedOperationException();
//						}
//					};
//					return iterator;
//				}
//			};
//		}
		
		
		
		public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
				final STATE hier, final LETTER letter) {
			return new Iterable<IncomingReturnTransition<LETTER, STATE>>() {
				@Override
				public Iterator<IncomingReturnTransition<LETTER, STATE>> iterator() {
					Iterator<IncomingReturnTransition<LETTER, STATE>> iterator = 
							new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
						Iterator<STATE> m_Iterator;
						{
							Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = m_ReturnIn;
							if (letter2hier2pred != null) {
								Map<STATE, Set<STATE>> hier2pred = letter2hier2pred.get(letter);
								if (hier2pred != null) {
									if (hier2pred.get(hier) != null) {
										m_Iterator = hier2pred.get(hier).iterator();
									} else {
										m_Iterator = null;
									}
								} else {
									m_Iterator = null;
								}
							} else {
								m_Iterator = null;
							}
						}
	
						@Override
						public boolean hasNext() {
							return m_Iterator == null || m_Iterator.hasNext();
						}
	
						@Override
						public IncomingReturnTransition<LETTER, STATE> next() {
							if (m_Iterator == null) {
								throw new NoSuchElementException();
							} else {
								STATE pred = m_Iterator.next(); 
								return new IncomingReturnTransition<LETTER, STATE>(pred, hier, letter);
							}
						}
	
						@Override
						public void remove() {
							throw new UnsupportedOperationException();
						}
					};
					return iterator;
				}
			};
		}
		
		
		public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
				final LETTER letter) {
			return new Iterable<IncomingReturnTransition<LETTER, STATE>>() {
				/**
				 * Iterates over all IncomingReturnTransition of succ.
				 * Iterates over all incoming return letters and uses the 
				 * iterators returned by returnPredecessors(hier, letter, succ)
				 */
				@Override
				public Iterator<IncomingReturnTransition<LETTER, STATE>> iterator() {
					Iterator<IncomingReturnTransition<LETTER, STATE>> iterator = 
							new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
						Iterator<STATE> m_HierIterator;
						STATE m_CurrentHier;
						Iterator<IncomingReturnTransition<LETTER, STATE>> m_CurrentIterator;
						{
							m_HierIterator = predReturnHier(letter).iterator();
							nextHier();
						}
	
						private void nextHier() {
							if (m_HierIterator.hasNext()) {
								do {
									m_CurrentHier = m_HierIterator.next();
									m_CurrentIterator = returnPredecessors(
											m_CurrentHier, letter).iterator();
								} while (!m_CurrentIterator.hasNext()
										&& m_HierIterator.hasNext());
								if (!m_CurrentIterator.hasNext()) {
									m_CurrentHier = null;
									m_CurrentIterator = null;
								}
							} else {
								m_CurrentHier = null;
								m_CurrentIterator = null;
							}
						}
	
						@Override
						public boolean hasNext() {
							return m_CurrentHier != null;
						}
	
						@Override
						public IncomingReturnTransition<LETTER, STATE> next() {
							if (m_CurrentHier == null) {
								throw new NoSuchElementException();
							} else {
								IncomingReturnTransition<LETTER, STATE> result = 
										m_CurrentIterator.next();
								if (!m_CurrentIterator.hasNext()) {
									nextHier();
								}
								return result;
							}
						}
	
						@Override
						public void remove() {
							throw new UnsupportedOperationException();
						}
					};
					return iterator;
				}
			};
		}
		
		
		public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors() {
			return new Iterable<IncomingReturnTransition<LETTER, STATE>>() {
				/**
				 * Iterates over all IncomingReturnTransition of succ.
				 * Iterates over all incoming return letters and uses the 
				 * iterators returned by returnPredecessors(letter, succ)
				 */
				@Override
				public Iterator<IncomingReturnTransition<LETTER, STATE>> iterator() {
					Iterator<IncomingReturnTransition<LETTER, STATE>> iterator = 
							new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
						Iterator<LETTER> m_LetterIterator;
						LETTER m_CurrentLetter;
						Iterator<IncomingReturnTransition<LETTER, STATE>> m_CurrentIterator;
						{
							m_LetterIterator = lettersReturnIncoming().iterator();
							nextLetter();
						}
	
						private void nextLetter() {
							if (m_LetterIterator.hasNext()) {
								do {
									m_CurrentLetter = m_LetterIterator.next();
									m_CurrentIterator = returnPredecessors(
											m_CurrentLetter).iterator();
								} while (!m_CurrentIterator.hasNext()
										&& m_LetterIterator.hasNext());
								if (!m_CurrentIterator.hasNext()) {
									m_CurrentLetter = null;
									m_CurrentIterator = null;
								}
							} else {
								m_CurrentLetter = null;
								m_CurrentIterator = null;
							}
						}
	
						@Override
						public boolean hasNext() {
							return m_CurrentLetter != null;
						}
	
						@Override
						public IncomingReturnTransition<LETTER, STATE> next() {
							if (m_CurrentLetter == null) {
								throw new NoSuchElementException();
							} else {
								IncomingReturnTransition<LETTER, STATE> result = 
										m_CurrentIterator.next();
								if (!m_CurrentIterator.hasNext()) {
									nextLetter();
								}
								return result;
							}
						}
	
						@Override
						public void remove() {
							throw new UnsupportedOperationException();
						}
					};
					return iterator;
				}
			};
		}
		
		
		
		public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
				final LETTER letter) {
			return new Iterable<OutgoingInternalTransition<LETTER, STATE>>() {
				@Override
				public Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator() {
					Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator = 
							new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
						Iterator<STATE> m_Iterator;
						{
							Map<LETTER, Set<STATE>> letter2succ = m_InternalOut;
							if (letter2succ != null) {
								if (letter2succ.get(letter) != null) {
									m_Iterator = letter2succ.get(letter).iterator();
								} else {
									m_Iterator = null;
								}
							} else {
								m_Iterator = null;
							}
						}
	
						@Override
						public boolean hasNext() {
							return m_Iterator == null || m_Iterator.hasNext();
						}
	
						@Override
						public OutgoingInternalTransition<LETTER, STATE> next() {
							if (m_Iterator == null) {
								throw new NoSuchElementException();
							} else {
								STATE succ = m_Iterator.next(); 
								return new OutgoingInternalTransition<LETTER, STATE>(letter, succ);
							}
						}
	
						@Override
						public void remove() {
							throw new UnsupportedOperationException();
						}
					};
					return iterator;
				}
			};
		}
		
		public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors() {
			return new Iterable<OutgoingInternalTransition<LETTER, STATE>>() {
				/**
				 * Iterates over all OutgoingInternalTransition of state.
				 * Iterates over all outgoing internal letters and uses the 
				 * iterators returned by internalSuccessors(state, letter)
				 */
				@Override
				public Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator() {
					Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator = 
							new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
						Iterator<LETTER> m_LetterIterator;
						LETTER m_CurrentLetter;
						Iterator<OutgoingInternalTransition<LETTER, STATE>> m_CurrentIterator;
						{
							m_LetterIterator = lettersInternal().iterator();
							nextLetter();
						}
	
						private void nextLetter() {
							if (m_LetterIterator.hasNext()) {
								do {
									m_CurrentLetter = m_LetterIterator.next();
									m_CurrentIterator = internalSuccessors(
											m_CurrentLetter).iterator();
								} while (!m_CurrentIterator.hasNext()
										&& m_LetterIterator.hasNext());
								if (!m_CurrentIterator.hasNext()) {
									m_CurrentLetter = null;
									m_CurrentIterator = null;
								}
							} else {
								m_CurrentLetter = null;
								m_CurrentIterator = null;
							}
						}
	
						@Override
						public boolean hasNext() {
							return m_CurrentLetter != null;
						}
	
						@Override
						public OutgoingInternalTransition<LETTER, STATE> next() {
							if (m_CurrentLetter == null) {
								throw new NoSuchElementException();
							} else {
								OutgoingInternalTransition<LETTER, STATE> result = 
										m_CurrentIterator.next();
								if (!m_CurrentIterator.hasNext()) {
									nextLetter();
								}
								return result;
							}
						}
	
						@Override
						public void remove() {
							throw new UnsupportedOperationException();
						}
					};
					return iterator;
				}
			};
		}
		
		
		
		
		
		
//		public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
//				final STATE state, final LETTER letter) {
//			return new Iterable<OutgoingCallTransition<LETTER, STATE>>() {
//				@Override
//				public Iterator<OutgoingCallTransition<LETTER, STATE>> iterator() {
//					Iterator<OutgoingCallTransition<LETTER, STATE>> iterator = 
//							new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
//						Iterator<STATE> m_Iterator;
//						{
//							Map<LETTER, Set<STATE>> letter2succ = m_CallOut.get(state);
//							if (letter2succ != null) {
//								if (letter2succ.get(letter) != null) {
//									m_Iterator = letter2succ.get(letter).iterator();
//								} else {
//									m_Iterator = null;
//								}
//							} else {
//								m_Iterator = null;
//							}
//						}
	//
//						@Override
//						public boolean hasNext() {
//							return m_Iterator == null || m_Iterator.hasNext();
//						}
	//
//						@Override
//						public OutgoingCallTransition<LETTER, STATE> next() {
//							if (m_Iterator == null) {
//								throw new NoSuchElementException();
//							} else {
//								STATE succ = m_Iterator.next(); 
//								return new OutgoingCallTransition<LETTER, STATE>(letter, succ);
//							}
//						}
	//
//						@Override
//						public void remove() {
//							throw new UnsupportedOperationException();
//						}
//					};
//					return iterator;
//				}
//			};
//		}
	//	
//		public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
//				final STATE state) {
//			return new Iterable<OutgoingCallTransition<LETTER, STATE>>() {
//				/**
//				 * Iterates over all OutgoingCallTransition of state.
//				 * Iterates over all outgoing call letters and uses the 
//				 * iterators returned by callSuccessors(state, letter)
//				 */
//				@Override
//				public Iterator<OutgoingCallTransition<LETTER, STATE>> iterator() {
//					Iterator<OutgoingCallTransition<LETTER, STATE>> iterator = 
//							new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
//						Iterator<LETTER> m_LetterIterator;
//						LETTER m_CurrentLetter;
//						Iterator<OutgoingCallTransition<LETTER, STATE>> m_CurrentIterator;
//						{
//							m_LetterIterator = lettersCall(state).iterator();
//							nextLetter();
//						}
	//
//						private void nextLetter() {
//							if (m_LetterIterator.hasNext()) {
//								do {
//									m_CurrentLetter = m_LetterIterator.next();
//									m_CurrentIterator = callSuccessors(state,
//											m_CurrentLetter).iterator();
//								} while (!m_CurrentIterator.hasNext()
//										&& m_LetterIterator.hasNext());
//								if (!m_CurrentIterator.hasNext()) {
//									m_CurrentLetter = null;
//									m_CurrentIterator = null;
//								}
//							} else {
//								m_CurrentLetter = null;
//								m_CurrentIterator = null;
//							}
//						}
	//
//						@Override
//						public boolean hasNext() {
//							return m_CurrentLetter != null;
//						}
	//
//						@Override
//						public OutgoingCallTransition<LETTER, STATE> next() {
//							if (m_CurrentLetter == null) {
//								throw new NoSuchElementException();
//							} else {
//								OutgoingCallTransition<LETTER, STATE> result = 
//										m_CurrentIterator.next();
//								if (!m_CurrentIterator.hasNext()) {
//									nextLetter();
//								}
//								return result;
//							}
//						}
	//
//						@Override
//						public void remove() {
//							throw new UnsupportedOperationException();
//						}
//					};
//					return iterator;
//				}
//			};
//		}
	//	
	//	
	//	
	//	
	//	
	//	
	//	
	//	
//		public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
//				final STATE state, final STATE hier, final LETTER letter) {
//			return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
//				@Override
//				public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
//					Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
//							new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
//						Iterator<STATE> m_Iterator;
//						{
//							Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succ = m_ReturnOut.get(state);
//							if (letter2hier2succ != null) {
//								Map<STATE, Set<STATE>> hier2succ = letter2hier2succ.get(letter);
//								if (hier2succ != null) {
//									if (hier2succ.get(hier) != null) {
//										m_Iterator = hier2succ.get(hier).iterator();
//									} else {
//										m_Iterator = null;
//									}
//								} else {
//									m_Iterator = null;
//								}
//							} else {
//								m_Iterator = null;
//							}
//						}
	//
//						@Override
//						public boolean hasNext() {
//							return m_Iterator == null || m_Iterator.hasNext();
//						}
	//
//						@Override
//						public OutgoingReturnTransition<LETTER, STATE> next() {
//							if (m_Iterator == null) {
//								throw new NoSuchElementException();
//							} else {
//								STATE succ = m_Iterator.next(); 
//								return new OutgoingReturnTransition<LETTER, STATE>(hier, letter, succ);
//							}
//						}
	//
//						@Override
//						public void remove() {
//							throw new UnsupportedOperationException();
//						}
//					};
//					return iterator;
//				}
//			};
//		}
	//	
	//	
//		public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
//				final STATE state, final LETTER letter) {
//			return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
//				/**
//				 * Iterates over all OutgoingReturnTransition of state.
//				 * Iterates over all outgoing return letters and uses the 
//				 * iterators returned by returnSuccecessors(state, letter)
//				 */
//				@Override
//				public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
//					Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
//							new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
//						Iterator<STATE> m_HierIterator;
//						STATE m_CurrentHier;
//						Iterator<OutgoingReturnTransition<LETTER, STATE>> m_CurrentIterator;
//						{
//							m_HierIterator = hierPred(state, letter).iterator();
//							nextHier();
//						}
	//
//						private void nextHier() {
//							if (m_HierIterator.hasNext()) {
//								do {
//									m_CurrentHier = m_HierIterator.next();
//									m_CurrentIterator = returnSucccessors(
//											state, m_CurrentHier, letter).iterator();
//								} while (!m_CurrentIterator.hasNext()
//										&& m_HierIterator.hasNext());
//								if (!m_CurrentIterator.hasNext()) {
//									m_CurrentHier = null;
//									m_CurrentIterator = null;
//								}
//							} else {
//								m_CurrentHier = null;
//								m_CurrentIterator = null;
//							}
//						}
	//
//						@Override
//						public boolean hasNext() {
//							return m_CurrentHier != null;
//						}
	//
//						@Override
//						public OutgoingReturnTransition<LETTER, STATE> next() {
//							if (m_CurrentHier == null) {
//								throw new NoSuchElementException();
//							} else {
//								OutgoingReturnTransition<LETTER, STATE> result = 
//										m_CurrentIterator.next();
//								if (!m_CurrentIterator.hasNext()) {
//									nextHier();
//								}
//								return result;
//							}
//						}
	//
//						@Override
//						public void remove() {
//							throw new UnsupportedOperationException();
//						}
//					};
//					return iterator;
//				}
//			};
//		}
	//	
//		public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
//				final STATE state, final STATE hier) {
//			return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
//				/**
//				 * Iterates over all OutgoingReturnTransition of state with 
//				 * hierarchical successor hier. 
//				 * Iterates over all outgoing return letters and uses the 
//				 * iterators returned by returnSuccecessors(state, hier, letter)
//				 */
//				@Override
//				public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
//					Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
//							new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
//						Iterator<LETTER> m_LetterIterator;
//						LETTER m_CurrentLetter;
//						Iterator<OutgoingReturnTransition<LETTER, STATE>> m_CurrentIterator;
//						{
//							m_LetterIterator = lettersReturn(state).iterator();
//							nextLetter();
//						}
	//
//						private void nextLetter() {
//							if (m_LetterIterator.hasNext()) {
//								do {
//									m_CurrentLetter = m_LetterIterator.next();
//									m_CurrentIterator = returnSucccessors(
//											state, hier, m_CurrentLetter).iterator();
//								} while (!m_CurrentIterator.hasNext()
//										&& m_LetterIterator.hasNext());
//								if (!m_CurrentIterator.hasNext()) {
//									m_CurrentLetter = null;
//									m_CurrentIterator = null;
//								}
//							} else {
//								m_CurrentLetter = null;
//								m_CurrentIterator = null;
//							}
//						}
	//
//						@Override
//						public boolean hasNext() {
//							return m_CurrentLetter != null;
//						}
	//
//						@Override
//						public OutgoingReturnTransition<LETTER, STATE> next() {
//							if (m_CurrentLetter == null) {
//								throw new NoSuchElementException();
//							} else {
//								OutgoingReturnTransition<LETTER, STATE> result = 
//										m_CurrentIterator.next();
//								if (!m_CurrentIterator.hasNext()) {
//									nextLetter();
//								}
//								return result;
//							}
//						}
	//
//						@Override
//						public void remove() {
//							throw new UnsupportedOperationException();
//						}
//					};
//					return iterator;
//				}
//			};
//		}
	//	
	//	
//		public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
//				final STATE state) {
//			return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
//				/**
//				 * Iterates over all OutgoingReturnTransition of state.
//				 * Iterates over all outgoing return letters and uses the 
//				 * iterators returned by returnSuccessors(state, letter)
//				 */
//				@Override
//				public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
//					Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
//							new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
//						Iterator<LETTER> m_LetterIterator;
//						LETTER m_CurrentLetter;
//						Iterator<OutgoingReturnTransition<LETTER, STATE>> m_CurrentIterator;
//						{
//							m_LetterIterator = lettersReturn(state).iterator();
//							nextLetter();
//						}
	//
//						private void nextLetter() {
//							if (m_LetterIterator.hasNext()) {
//								do {
//									m_CurrentLetter = m_LetterIterator.next();
//									m_CurrentIterator = returnSuccessors(state,
//											m_CurrentLetter).iterator();
//								} while (!m_CurrentIterator.hasNext()
//										&& m_LetterIterator.hasNext());
//								if (!m_CurrentIterator.hasNext()) {
//									m_CurrentLetter = null;
//									m_CurrentIterator = null;
//								}
//							} else {
//								m_CurrentLetter = null;
//								m_CurrentIterator = null;
//							}
//						}
	//
//						@Override
//						public boolean hasNext() {
//							return m_CurrentLetter != null;
//						}
	//
//						@Override
//						public OutgoingReturnTransition<LETTER, STATE> next() {
//							if (m_CurrentLetter == null) {
//								throw new NoSuchElementException();
//							} else {
//								OutgoingReturnTransition<LETTER, STATE> result = 
//										m_CurrentIterator.next();
//								if (!m_CurrentIterator.hasNext()) {
//									nextLetter();
//								}
//								return result;
//							}
//						}
	//
//						@Override
//						public void remove() {
//							throw new UnsupportedOperationException();
//						}
//					};
//					return iterator;
//				}
//			};
//		}
	}

}
