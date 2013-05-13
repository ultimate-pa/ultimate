package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

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

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;

public class ReachableStatesAutomaton<LETTER,STATE> implements INestedWordAutomaton<LETTER,STATE>, INWA<LETTER,STATE> {

	
	private final NestedWordAutomaton<LETTER,STATE> m_Operand;
	
	private final Collection<LETTER> m_InternalAlphabet;
	private final Collection<LETTER> m_CallAlphabet;
	private final Collection<LETTER> m_ReturnAlphabet;
	
	protected final StateFactory<STATE> m_StateFactory;
	
	private final Map<STATE,StateContainer> m_States = 
			new HashMap<STATE,StateContainer>();
	
	private final Set<STATE> m_initialStates = new HashSet<STATE>();
	
	private final DoubleDeckerWorklist doubleDeckerWorklist = new DoubleDeckerWorklist();
	private final CecSplitWorklist cecSplitWorklist = new CecSplitWorklist();
	
	private final Map<STATE,Entry> m_State2Entry = new HashMap<STATE,Entry>();

	private LinkedList<StateContainer> worklist;

	private HashSet<STATE> visited; 
	
	private Map<STATE,Set<STATE>> m_Summaries = new HashMap<STATE,Set<STATE>>();
	
	private List<CommonEntriesComponent> m_AllCECs = new ArrayList<CommonEntriesComponent>();
	
	public void addSummary(STATE callPred, STATE returnSucc) {
		Set<STATE> returnSuccs = m_Summaries.get(callPred);
		if (returnSucc == null) {
			returnSuccs = new HashSet<STATE>();
			m_Summaries.put(callPred, returnSuccs);
		}
		returnSuccs.add(returnSucc);
	}
	
	public ReachableStatesAutomaton(INestedWordAutomaton<LETTER,STATE> operand) {
		this.m_Operand = (NestedWordAutomaton<LETTER, STATE>) operand;
		m_InternalAlphabet = operand.getAlphabet();
		m_CallAlphabet = operand.getCallAlphabet();
		m_ReturnAlphabet = operand.getReturnAlphabet();
		m_StateFactory = operand.getStateFactory();
		addInitialStates(m_Operand.getInitialStates());
		buildAllStates();
		assert(checkTransitionsReturnedConsistent());
		assert(worklist.isEmpty());
		assert(doubleDeckerWorklist.isEmpty());
		assert(cecSplitWorklist.isEmtpy());
		assert(allStatesAreInTheirCec());
		assert(cecSumConsistent());
		for (CommonEntriesComponent cec : m_AllCECs) {
			assert (occuringStatesAreConsistent(cec));
		}
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
			m_State2Entry.put(state, this);
		}
		
		public STATE getState() {
			return m_State;
		}
		
		public String toString() {
			return m_State.toString();
		}
	}
	
	public class CommonEntriesComponent {
		int m_Size = 0;
		final Set<Entry> m_Entries;
		final Set<STATE> m_DownStates;
		final Set<STATE> m_ReturnOutCandidates;
		final Map<STATE,Set<STATE>> m_BorderOut;
		
				
		public CommonEntriesComponent(HashSet<Entry> entries, HashSet<STATE> downStates) {
			this.m_Entries = entries;
			this.m_DownStates = downStates;
			this.m_ReturnOutCandidates = new HashSet<STATE>();
			this.m_BorderOut = new HashMap<STATE,Set<STATE>>();
			m_AllCECs.add(this);
		}
		
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append("Entries: ").append(m_Entries).append("\n");
			sb.append("DownStates: ").append(m_DownStates).append("\n");
			sb.append("Size: ").append(m_Size).append("\n");
			sb.append("ReturnOutCandiates: ").append(m_ReturnOutCandidates).append("\n");
			sb.append("BorderOut: ").append(m_BorderOut).append("\n");
			return sb.toString();
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
	
	
	private StateContainer constructStateContainer(STATE state, CommonEntriesComponent cec) {
		StateContainer result = new StateContainer(state, cec);
		cec.m_Size++;
		if (candidateForOutgoingReturn(state)) {
			cec.addReturnOutCandicate(state);
		}
		return result;
	}
	
	private void addInitialStates(Iterable<STATE> initialStates) {
		for (STATE state : initialStates) {
			this.m_initialStates.add(state);
			Entry entry = new Entry(state);
			HashSet<Entry> entries = new HashSet<Entry>(1);
			entries.add(entry);
			HashSet<STATE> downStates = new HashSet<STATE>();
			downStates.add(getEmptyStackState());
			CommonEntriesComponent cec = new CommonEntriesComponent(entries,downStates);
			StateContainer sc = constructStateContainer(state, cec);
			m_States.put(state, sc);
		}
		
	}
	
	
	private boolean candidateForOutgoingReturn(STATE state) {
		return true;
	}
	
	
	private class CecSplitWorklist {
		List<Object[]> m_worklist = new LinkedList<Object[]>();
		
		private boolean isEmtpy() {
			return m_worklist.isEmpty();
		}
		
		public void add(STATE state, CommonEntriesComponent cec, Set<Entry> entries, Set<STATE> downStates) {
			Object[] elem = new Object[] { state, cec, entries, downStates };
			m_worklist.add(elem);
		}
		
		private void processFirst() {
			Object[] elem = m_worklist.remove(0);
			STATE state = (STATE) elem[0];
			CommonEntriesComponent cec = (CommonEntriesComponent) elem[1]; 
			Set<Entry> entries = (Set<Entry>) elem[2];
			Set<STATE> downStates = (Set<STATE>) elem[3];
			HashSet<STATE> splitStates = new HashSet<STATE>();
			splitStates.add(state);
			updateCECs(splitStates, cec, entries, downStates);
		}
		
		public void processAll() {
			while (!isEmtpy()) {
				processFirst();
			}
		}
	}

	
	
	public static <E> boolean isSubset(Set<E> lhs, Set<E> rhs) {
		for (E elem : lhs) {
			if (!rhs.contains(elem)) {
				return false;
			}
		}
		return true;
	}
	
	private CommonEntriesComponent updateCECs(Set<STATE> splitStarts, 
			CommonEntriesComponent oldCec, Set<Entry> newEntries, Set<STATE> newDownStates) {
		if (isSubset(newEntries, oldCec.getEntries())) {
			assert (isSubset(newDownStates, oldCec.getDownStates()));
			return oldCec;
		}
		
		HashSet<Entry> entries = new HashSet<Entry>();
		entries.addAll(oldCec.getEntries());
		entries.addAll(newEntries);
		HashSet<STATE> downStates = new HashSet<STATE>();
		downStates.addAll(oldCec.getDownStates());
		downStates.addAll(newDownStates);
		CommonEntriesComponent result = new CommonEntriesComponent(entries, downStates);
		
		Set<STATE> visited = new HashSet<STATE>();
		List<STATE> worklist = new LinkedList<STATE>();
		for (STATE splitStart : splitStarts) {
			assert(m_States.get(splitStart).getCommonEntriesComponent() == oldCec);
			worklist.add(splitStart);
		}
		while (!worklist.isEmpty()) {
			STATE state = worklist.remove(0);
			visited.add(state);
			if (oldCec.getReturnOutCandidates().contains(state)) {
				result.addReturnOutCandicate(state);
				oldCec.removeReturnOutCandicate(state);
				for(STATE down : newDownStates) {
					doubleDeckerWorklist.enqueue(state, down);
				}
			}
			if (oldCec.isBorderState(state)) {
				Set<STATE> foreigners = oldCec.getForeigners(state);
				result.m_BorderOut.put(state, foreigners);
				oldCec.m_BorderOut.remove(state);
				for (STATE foreigner : foreigners) {
					StateContainer foreignerSC = m_States.get(foreigner);
					CommonEntriesComponent foreignerCec = foreignerSC.getCommonEntriesComponent();
					cecSplitWorklist.add(foreigner, foreignerCec, entries, downStates);
				}
			}
			StateContainer stateSc = m_States.get(state);
			stateSc.setCommonEntriesComponent(result);
			assert oldCec.m_Size > 0;
			oldCec.m_Size--;
			result.m_Size++;
			
			for (OutgoingInternalTransition<LETTER, STATE> trans : stateSc.internalSuccessors()) {
				STATE succ = trans.getSucc();
				StateContainer succSc = m_States.get(succ);
				if (succSc.getCommonEntriesComponent() == oldCec) {
					if (!visited.contains(succ)) {
						worklist.add(succ);
					}
				}
			}
			if (m_Summaries.containsKey(state)) {
				for (STATE succ : m_Summaries.get(state)) {
					StateContainer succSc = m_States.get(succ);
					if (succSc.getCommonEntriesComponent() == oldCec) {
						if (!visited.contains(succ)) {
							worklist.add(succ);
						}
					}
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
		return result;
	}
	
	
	private void buildAllStates() {
		worklist = new LinkedList<StateContainer>();
		visited = new HashSet<STATE>();
		
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
				StateContainer succSC = m_States.get(succ);
				if (succSC == null) {
					succSC = constructStateContainer(succ, stateCec);
					m_States.put(succ, succSC);
				} else {
					CommonEntriesComponent succCEC = succSC.getCommonEntriesComponent();
					if (stateCec != succCEC) {
						Set<Entry> newEntries = new HashSet<Entry>();
						newEntries.addAll(stateCec.getEntries());
						newEntries.removeAll(succCEC.getEntries());						
						Set<STATE> newDownStates = new HashSet<STATE>();
						newDownStates.addAll(stateCec.getDownStates());
						newDownStates.removeAll(succCEC.getDownStates());
						Set<STATE> splitStates = new HashSet<STATE>();
						splitStates.add(succ);
						updateCECs(splitStates, succCEC, newEntries, newDownStates);
						stateCec.addBorderCrossing(state, succ);
						cecSplitWorklist.processAll();
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
				StateContainer succSC = m_States.get(succ);
				HashSet<STATE> downStates = new HashSet<STATE>();
				downStates.add(state);
				if (succSC == null) {
					Entry entry = new Entry(succ);
					HashSet<Entry> entries = new HashSet<Entry>();
					entries.add(entry);
					CommonEntriesComponent succCEC = new CommonEntriesComponent(entries, downStates);
					succSC = constructStateContainer(succ, succCEC);
					m_States.put(succ, succSC);
				} else {
					CommonEntriesComponent succCEC = succSC.getCommonEntriesComponent();
					Entry entry = m_State2Entry.get(succ);
					if (succCEC.getEntries().contains(entry)) {
						updateCECs(succCEC, downStates);
					} else {
						HashSet<Entry> entries = new HashSet<Entry>();
						entries.add(entry);
						downStates.removeAll(succCEC.getDownStates());
						Set<STATE> splitStarts = new HashSet<STATE>();
						splitStarts.add(succ);
						updateCECs(splitStarts, succCEC, entries, downStates);
						cecSplitWorklist.processAll();
					}
					sc.addCallOutgoing(trans);
					succSC.addCallIncoming(new IncomingCallTransition<LETTER, STATE>(state, trans.getLetter()));
					if (!visited.contains(succ)) {
						worklist.add(succSC);
					}
				}
			}

			StateContainer stateSc = m_States.get(state);
			CommonEntriesComponent stateCEC = stateSc.getCommonEntriesComponent();
			//TODO: need copy to avoid concurModExcpetion ???
			for (STATE down : stateCEC.getDownStates()) {
				if (down != getEmptyStackState()) {
					StateContainer downSC = m_States.get(down);
					addReturnAndSuccessor(stateSc, downSC);
				}
			}
			
			while (!doubleDeckerWorklist.isEmpty()) {
				DoubleDecker<STATE> doubleDecker = doubleDeckerWorklist.dequeue();
				StateContainer upSC  = m_States.get(doubleDecker.getUp());
				StateContainer downSC  = m_States.get(doubleDecker.getDown());
				addReturnAndSuccessor(upSC, downSC);
			}
		}
	}
	
	
	
	
	private void updateCECs(CommonEntriesComponent startCec,
			HashSet<STATE> downStates) {
		List<CommonEntriesComponent> worklist = new LinkedList<CommonEntriesComponent>(); 
		Set<CommonEntriesComponent> visitedCECs = new HashSet<CommonEntriesComponent>();
		worklist.add(startCec);
		while(!worklist.isEmpty()) {
			CommonEntriesComponent cec = worklist.remove(0);
			visitedCECs.add(cec);
			HashSet<STATE> newdownStates = new HashSet<STATE>();
			for (STATE down : downStates) {
				if (!cec.getDownStates().contains(down)) {
					newdownStates.add(down);
				}
			}
			if(!newdownStates.isEmpty()) {
				for (STATE state : cec.getReturnOutCandidates()) {
					for (STATE down : newdownStates) {
						doubleDeckerWorklist.enqueue(state, down);
						cec.addDownState(down);
					}
				}
				for (STATE resident : cec.m_BorderOut.keySet()) {
					for (STATE foreigner : cec.m_BorderOut.get(resident)) {
						CommonEntriesComponent foreignerCec = 
								m_States.get(foreigner).getCommonEntriesComponent();
						if (!visitedCECs.contains(foreignerCec)) {
							worklist.add(foreignerCec);
						}
					}
				}

			}
		}
	}

	private void addReturnAndSuccessor(StateContainer stateSc, StateContainer downSc) {
		STATE down = downSc.getState();
		CommonEntriesComponent downCec = downSc.getCommonEntriesComponent();
		for (OutgoingReturnTransition<LETTER, STATE> trans : stateSc.returnSuccessorsGivenHier(down)) {
			STATE succ = trans.getSucc();
			StateContainer succSC = m_States.get(succ);
			if (succSC == null) {
				succSC = constructStateContainer(succ, downCec);
				m_States.put(succ, succSC);
			} else {
				CommonEntriesComponent succCEC = succSC.getCommonEntriesComponent();
				if (downCec != succCEC) {
					Set<Entry> newEntries = new HashSet<Entry>();
					newEntries.addAll(downCec.getEntries());
					newEntries.removeAll(succCEC.getEntries());						
					Set<STATE> newDownStates = new HashSet<STATE>();
					newDownStates.addAll(downCec.getDownStates());
					newDownStates.removeAll(succCEC.getDownStates());
					Set<STATE> splitStates = new HashSet<STATE>();
					splitStates.add(succ);
					updateCECs(splitStates, succCEC, newEntries, newDownStates);
					downCec.addBorderCrossing(down, succ);
					cecSplitWorklist.processAll();
				}
			}
			stateSc.addReturnOutgoing(trans);
			succSC.addReturnIncoming(new IncomingReturnTransition<LETTER, STATE>(stateSc.getState(), down, trans.getLetter()));
			if (!visited.contains(succ)) {
				worklist.add(succSC);
			}
		}
	}
	

//	private void addNewlyEnabledReturnTransitions(
//			CommonEntriesComponent cec, STATE state) {
//		List<CommonEntriesComponent> worklist = new LinkedList<CommonEntriesComponent>(); 
//		Set<CommonEntriesComponent> visitedCECs = new HashSet<CommonEntriesComponent>();
//		
//		
//	}

//	private CommonEntriesComponent computeCec(STATE state, CommonEntriesComponent stateCec,
//			STATE succ, CommonEntriesComponent succCEC) {
//		if (succCEC == null) {
//			return stateCec;
//		} else if (succCEC == stateCec) {
//			return stateCec;
//		} else {
//			CommonEntriesComponent result = new CommonEntriesComponent(succCEC, stateCec);
//			Set<STATE> newDownStates = stateCec.getDownStates();
//			newDownStates.removeAll(succCEC.getDownStates());
//			updateCECs(succ, result, stateCec, newDownStates);
//			stateCec.addBorderCrossing(state, succ);
//			return result;
//		}
//	}

	
	@Override
	public IRun<LETTER, STATE> acceptingRun() throws OperationCanceledException {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean accepts(Word<LETTER> word) {
		throw new UnsupportedOperationException();
	}

	@Override
	public int size() {
		return m_States.size();
	}

	@Override
	public Collection<LETTER> getAlphabet() {
		return m_InternalAlphabet;
	}

	@Override
	public String sizeInformation() {
		int states = m_States.size();
		return states + " states.";
	}

	@Override
	public Collection<LETTER> getInternalAlphabet() {
		return m_InternalAlphabet;
	}

	@Override
	public Collection<LETTER> getCallAlphabet() {
		return m_CallAlphabet;
	}

	@Override
	public Collection<LETTER> getReturnAlphabet() {
		return m_ReturnAlphabet;
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return m_StateFactory;
	}

	@Override
	public Collection<STATE> getStates() {
		return m_States.keySet();
	}

	@Override
	public Collection<STATE> getInitialStates() {
		return m_initialStates;
	}

	@Override
	public Collection<STATE> getFinalStates() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isInitial(STATE state) {
		return m_Operand.isInitial(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		return m_Operand.isFinal(state);
	}

	@Override
	public void addState(boolean isInitial, boolean isFinal, STATE state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void removeState(STATE state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public STATE getEmptyStackState() {
		return m_Operand.getEmptyStackState();
	}

	@Override
	public Collection<LETTER> lettersInternal(STATE state) {
		return m_States.get(state).lettersInternal();
	}

	@Override
	public Collection<LETTER> lettersCall(STATE state) {
		return m_States.get(state).lettersCall();
	}

	@Override
	public Collection<LETTER> lettersReturn(STATE state) {
		return m_States.get(state).lettersReturn();
	}

	@Override
	public Collection<LETTER> lettersInternalIncoming(STATE state) {
		return m_States.get(state).lettersInternalIncoming();
	}

	@Override
	public Collection<LETTER> lettersCallIncoming(STATE state) {
		return m_States.get(state).lettersCallIncoming();
	}

	@Override
	public Collection<LETTER> lettersReturnIncoming(STATE state) {
		return m_States.get(state).lettersReturnIncoming();
	}

	@Override
	public Collection<LETTER> lettersReturnSummary(STATE state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<STATE> succInternal(STATE state, LETTER letter) {
		return m_States.get(state).succInternal(letter);
	}

	@Override
	public Iterable<STATE> succCall(STATE state, LETTER letter) {
		return m_States.get(state).succCall(letter);
	}

	@Override
	public Iterable<STATE> hierPred(STATE state, LETTER letter) {
		return m_States.get(state).hierPred(letter);
	}

	@Override
	public Iterable<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
		return m_States.get(state).succReturn(hier, letter);
	}

	@Override
	public Iterable<STATE> predInternal(STATE state, LETTER letter) {
		return m_States.get(state).predInternal(letter);
	}

	@Override
	public Iterable<STATE> predCall(STATE state, LETTER letter) {
		return m_States.get(state).predCall(letter);
	}

	@Override
	public Iterable<STATE> predReturnLin(STATE state, LETTER letter, STATE hier) {
		return m_States.get(state).predReturnLin(letter, hier);
	}

	@Override
	public Iterable<STATE> predReturnHier(STATE state, LETTER letter) {
		return m_States.get(state).predReturnHier(letter);
	}

	@Override
	public void addInternalTransition(STATE pred, LETTER letter, STATE succ) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void addCallTransition(STATE pred, LETTER letter, STATE succ) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void addReturnTransition(STATE pred, STATE hier, LETTER letter,
			STATE succ) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean finalIsTrap() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isDeterministic() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isTotal() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> getSummaryReturnTransitions(
			LETTER letter, STATE hier) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> getIncomingReturnTransitions(
			LETTER letter, STATE hier) {
		return m_States.get(hier).getIncomingReturnTransitions(letter);
	}
	
	
	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			LETTER letter, STATE succ) {
		return m_States.get(succ).internalPredecessors(letter);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			STATE succ) {
		return m_States.get(succ).internalPredecessors();
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			LETTER letter, STATE succ) {
		return m_States.get(succ).callPredecessors(letter);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			STATE succ) {
		return m_States.get(succ).callPredecessors();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		return m_States.get(state).internalSuccessors(letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state) {
		return m_States.get(state).internalSuccessors();
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state, LETTER letter) {
		return m_States.get(state).callSuccessors(letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state) {
		return m_States.get(state).callSuccessors();
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			STATE hier, LETTER letter, STATE succ) {
		return m_States.get(succ).returnPredecessors(hier, letter);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			LETTER letter, STATE succ) {
		return m_States.get(succ).getIncomingReturnTransitions(letter);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			STATE succ) {
		return m_States.get(succ).returnPredecessors();
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			STATE state, STATE hier, LETTER letter) {
		return m_States.get(state).returnSucccessors(hier, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			STATE state, LETTER letter) {
		return m_States.get(state).returnSuccessors(letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			STATE state) {
		return m_States.get(state).returnSuccessors();
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier) {
		return m_States.get(state).returnSuccessorsGivenHier(hier);
	}
	
	
	
	
	/**
	 * Contains STATES and information of transitions.
	 *
	 * @param <LETTER>
	 * @param <STATE>
	 */
	public class StateContainer {
		
		
		private final STATE m_State;
		
		public String toString() {
			return m_State.toString();
		}
		
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
		
		boolean isEntry() {
			for (Entry entry : this.cec.getEntries()) {
				if (entry.getState().equals(this)) {
					return true;
				}
			}
			return false;
		}
		
		
		
		public void addInternalOutgoing(OutgoingInternalTransition<LETTER, STATE> internalOutgoing) {
			LETTER letter = internalOutgoing.getLetter();
			STATE succ = internalOutgoing.getSucc();
			if (m_InternalOut == null) {
				m_InternalOut = new HashMap<LETTER, Set<STATE>>();
			}
			Set<STATE> succs = m_InternalOut.get(letter);
			if (succs == null) {
				succs = new HashSet<STATE>();
				m_InternalOut.put(letter, succs);
			}
			succs.add(succ);
		}
		
		public void addInternalIncoming(IncomingInternalTransition<LETTER, STATE> internalIncoming) {
			LETTER letter = internalIncoming.getLetter();
			STATE pred = internalIncoming.getPred();
			if (m_InternalIn == null) {
				m_InternalIn = new HashMap<LETTER, Set<STATE>>();
			}
			Set<STATE> preds = m_InternalIn.get(letter);
			if (preds == null) {
				preds = new HashSet<STATE>();
				m_InternalIn.put(letter,preds);
			}
			preds.add(pred);
		}
		
		public void addCallOutgoing(OutgoingCallTransition<LETTER, STATE> callOutgoing) {
			LETTER letter = callOutgoing.getLetter();
			STATE succ = callOutgoing.getSucc();
			if (m_CallOut == null) {
				m_CallOut = new HashMap<LETTER, Set<STATE>>();
			}
			Set<STATE> succs = m_CallOut.get(letter);
			if (succs == null) {
				succs = new HashSet<STATE>();
				m_CallOut.put(letter,succs);
			}
			succs.add(succ);
		}
		
		public void addCallIncoming(IncomingCallTransition<LETTER, STATE> callIncoming) {
			LETTER letter = callIncoming.getLetter();
			STATE pred = callIncoming.getPred();
			if (m_CallIn == null) {
				m_CallIn = new HashMap<LETTER, Set<STATE>>();
			}
			Set<STATE> preds = m_CallIn.get(letter);
			if (preds == null) {
				preds = new HashSet<STATE>();
				m_CallIn.put(letter,preds);
			}
			preds.add(pred);
		}
		
		public void addReturnOutgoing(OutgoingReturnTransition<LETTER, STATE> returnOutgoing) {
			LETTER letter = returnOutgoing.getLetter();
			STATE hier = returnOutgoing.getHierPred();
			STATE succ = returnOutgoing.getSucc();
			if (m_ReturnOut == null) {
				m_ReturnOut = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
			}
			Map<STATE, Set<STATE>> hier2succs = m_ReturnOut.get(letter);
			if (hier2succs == null) {
				hier2succs = new HashMap<STATE, Set<STATE>>();
				m_ReturnOut.put(letter, hier2succs);
			}
			Set<STATE> succs = hier2succs.get(hier);
			if (succs == null) {
				succs = new HashSet<STATE>();
				hier2succs.put(hier, succs);
			}
			succs.add(succ);
		}
		
		public void addReturnIncoming(IncomingReturnTransition<LETTER, STATE> returnIncoming) {
			LETTER letter = returnIncoming.getLetter();
			STATE hier = returnIncoming.getHierPred();
			STATE pred = returnIncoming.getLinPred();
			if (m_ReturnIn == null) {
				m_ReturnIn = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
			}
			Map<STATE, Set<STATE>> hier2preds = m_ReturnIn.get(letter);
			if (hier2preds == null) {
				hier2preds = new HashMap<STATE, Set<STATE>>();
				m_ReturnIn.put(letter, hier2preds);
			}
			Set<STATE> preds = hier2preds.get(hier);
			if (preds == null) {
				preds = new HashSet<STATE>();
				hier2preds.put(hier, preds);
			}
			preds.add(pred);
		}
		

//		@Override
//		public void addReturnTransition(STATE pred, STATE hier, LETTER letter, STATE succ) {
//			assert contains(pred);
//			assert contains(hier);
//			assert contains(succ);
//
//			
//			Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = m_ReturnSummary.get(hier);
//			if (letter2pred2succs == null) {
//				letter2pred2succs = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
//				m_ReturnSummary.put(hier, letter2pred2succs);
//			}
//			Map<STATE, Set<STATE>> pred2succs = letter2pred2succs.get(letter);
//			if (pred2succs == null) {
//				pred2succs = new HashMap<STATE, Set<STATE>>();
//				letter2pred2succs.put(letter, pred2succs);
//			}
//			Set<STATE> succS = pred2succs.get(pred);
//			if (succS == null) {
//				succS = new HashSet<STATE>();
//				pred2succs.put(pred, succS);
//			}
//			succS.add(succ);
//			// assert checkTransitionsStoredConsistent();
//		}
		
		
		

		

		


		
		
		
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
		
		
		public Collection<STATE> succInternal(LETTER letter) {
			Map<LETTER, Set<STATE>> map = m_InternalOut;
			if (map == null) {
				return m_EmptySetOfStates;
			}
			Set<STATE> result = map.get(letter);
			return result == null ? m_EmptySetOfStates : result;
		}
		
		public Collection<STATE> predInternal(LETTER letter) {
			Map<LETTER, Set<STATE>> map = m_InternalIn;
			if (map == null) {
				return m_EmptySetOfStates;
			}
			Set<STATE> result = map.get(letter);
			return result == null ? m_EmptySetOfStates : result;
		}
		
		public Collection<STATE> succCall(LETTER letter) {
			Map<LETTER, Set<STATE>> map = m_CallOut;
			if (map == null) {
				return m_EmptySetOfStates;
			}
			Set<STATE> result = map.get(letter);
			return result == null ? m_EmptySetOfStates : result;
		}
		
		public Collection<STATE> predCall(LETTER letter) {
			Map<LETTER, Set<STATE>> map = m_CallIn;
			if (map == null) {
				return m_EmptySetOfStates;
			}
			Set<STATE> result = map.get(letter);
			return result == null ? m_EmptySetOfStates : result;
		}
		
		public Collection<STATE> hierPred(LETTER letter) {
			Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnOut;
			if (map == null) {
				return m_EmptySetOfStates;
			}
			 Map<STATE, Set<STATE>> hier2succs = map.get(letter);
			return hier2succs == null ? m_EmptySetOfStates : hier2succs.keySet();
		}
		
		public Collection<STATE> succReturn(STATE hier, LETTER letter) {
			Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnOut;
			if (map == null) {
				return m_EmptySetOfStates;
			}
			Map<STATE, Set<STATE>> hier2succs = map.get(letter);
			if (hier2succs == null) {
				return m_EmptySetOfStates;
			}
			Set<STATE> result = hier2succs.get(hier);
			return result == null ? m_EmptySetOfStates : result;
		}
		
		public Collection<STATE> predReturnLin(LETTER letter, STATE hier) {
			Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds  = m_ReturnIn;
			if (letter2hier2preds == null) {
				return m_EmptySetOfStates;
			}
			Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
			if (hier2preds == null) {
				return m_EmptySetOfStates;
			}
			Set<STATE> result = hier2preds.get(hier);
			return result == null ? m_EmptySetOfStates : result;
		}
		
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

		public Iterable<IncomingReturnTransition<LETTER, STATE>> 
							getIncomingReturnTransitions(LETTER letter) {
			Set<IncomingReturnTransition<LETTER, STATE>> result = 
					new HashSet<IncomingReturnTransition<LETTER, STATE>>();
			Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = 
					m_ReturnIn;
			if (letter2hier2pred == null) {
				return result;
			}
			Map<STATE, Set<STATE>> hier2pred = letter2hier2pred.get(letter);
			if (hier2pred == null) {
				return result;
			}
			for (STATE hier : hier2pred.keySet()) {
				if (hier2pred.get(hier) != null) {
					for (STATE pred : hier2pred.get(hier)) {
						IncomingReturnTransition<LETTER, STATE> srt = 
						new IncomingReturnTransition<LETTER, STATE>(pred, hier, letter);
					result.add(srt);
					}
				}
			}
			return result;
		}
		
		
		
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
		
		
		
		
		
		public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
				final LETTER letter) {
			return new Iterable<IncomingCallTransition<LETTER, STATE>>() {
				@Override
				public Iterator<IncomingCallTransition<LETTER, STATE>> iterator() {
					Iterator<IncomingCallTransition<LETTER, STATE>> iterator = 
							new Iterator<IncomingCallTransition<LETTER, STATE>>() {
						Iterator<STATE> m_Iterator;
						{
							Map<LETTER, Set<STATE>> letter2pred = m_CallIn;
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
						public IncomingCallTransition<LETTER, STATE> next() {
							if (m_Iterator == null) {
								throw new NoSuchElementException();
							} else {
								STATE pred = m_Iterator.next(); 
								return new IncomingCallTransition<LETTER, STATE>(pred, letter);
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
		
		
		
		public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors() {
			return new Iterable<IncomingCallTransition<LETTER, STATE>>() {
				/**
				 * Iterates over all IncomingCallTransition of succ.
				 * Iterates over all incoming call letters and uses the 
				 * iterators returned by callPredecessors(letter, succ)
				 */
				@Override
				public Iterator<IncomingCallTransition<LETTER, STATE>> iterator() {
					Iterator<IncomingCallTransition<LETTER, STATE>> iterator = 
							new Iterator<IncomingCallTransition<LETTER, STATE>>() {
						Iterator<LETTER> m_LetterIterator;
						LETTER m_CurrentLetter;
						Iterator<IncomingCallTransition<LETTER, STATE>> m_CurrentIterator;
						{
							m_LetterIterator = lettersCallIncoming().iterator();
							nextLetter();
						}
	
						private void nextLetter() {
							if (m_LetterIterator.hasNext()) {
								do {
									m_CurrentLetter = m_LetterIterator.next();
									m_CurrentIterator = callPredecessors(
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
						public IncomingCallTransition<LETTER, STATE> next() {
							if (m_CurrentLetter == null) {
								throw new NoSuchElementException();
							} else {
								IncomingCallTransition<LETTER, STATE> result = 
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
		
		
		
		
		
		
		public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
				final LETTER letter) {
			return new Iterable<OutgoingCallTransition<LETTER, STATE>>() {
				@Override
				public Iterator<OutgoingCallTransition<LETTER, STATE>> iterator() {
					Iterator<OutgoingCallTransition<LETTER, STATE>> iterator = 
							new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
						Iterator<STATE> m_Iterator;
						{
							Map<LETTER, Set<STATE>> letter2succ = m_CallOut;
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
						public OutgoingCallTransition<LETTER, STATE> next() {
							if (m_Iterator == null) {
								throw new NoSuchElementException();
							} else {
								STATE succ = m_Iterator.next(); 
								return new OutgoingCallTransition<LETTER, STATE>(letter, succ);
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
		
		public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors() {
			return new Iterable<OutgoingCallTransition<LETTER, STATE>>() {
				/**
				 * Iterates over all OutgoingCallTransition of state.
				 * Iterates over all outgoing call letters and uses the 
				 * iterators returned by callSuccessors(state, letter)
				 */
				@Override
				public Iterator<OutgoingCallTransition<LETTER, STATE>> iterator() {
					Iterator<OutgoingCallTransition<LETTER, STATE>> iterator = 
							new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
						Iterator<LETTER> m_LetterIterator;
						LETTER m_CurrentLetter;
						Iterator<OutgoingCallTransition<LETTER, STATE>> m_CurrentIterator;
						{
							m_LetterIterator = lettersCall().iterator();
							nextLetter();
						}
	
						private void nextLetter() {
							if (m_LetterIterator.hasNext()) {
								do {
									m_CurrentLetter = m_LetterIterator.next();
									m_CurrentIterator = callSuccessors(m_CurrentLetter).iterator();
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
						public OutgoingCallTransition<LETTER, STATE> next() {
							if (m_CurrentLetter == null) {
								throw new NoSuchElementException();
							} else {
								OutgoingCallTransition<LETTER, STATE> result = 
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
		
		
		
		
		
		
		
		
		public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
				final STATE hier, final LETTER letter) {
			return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
				@Override
				public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
					Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
							new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
						Iterator<STATE> m_Iterator;
						{
							Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succ = m_ReturnOut;
							if (letter2hier2succ != null) {
								Map<STATE, Set<STATE>> hier2succ = letter2hier2succ.get(letter);
								if (hier2succ != null) {
									if (hier2succ.get(hier) != null) {
										m_Iterator = hier2succ.get(hier).iterator();
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
						public OutgoingReturnTransition<LETTER, STATE> next() {
							if (m_Iterator == null) {
								throw new NoSuchElementException();
							} else {
								STATE succ = m_Iterator.next(); 
								return new OutgoingReturnTransition<LETTER, STATE>(hier, letter, succ);
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
		
		
		public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
				final LETTER letter) {
			return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
				/**
				 * Iterates over all OutgoingReturnTransition of state.
				 * Iterates over all outgoing return letters and uses the 
				 * iterators returned by returnSuccecessors(state, letter)
				 */
				@Override
				public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
					Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
							new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
						Iterator<STATE> m_HierIterator;
						STATE m_CurrentHier;
						Iterator<OutgoingReturnTransition<LETTER, STATE>> m_CurrentIterator;
						{
							m_HierIterator = hierPred(letter).iterator();
							nextHier();
						}
	
						private void nextHier() {
							if (m_HierIterator.hasNext()) {
								do {
									m_CurrentHier = m_HierIterator.next();
									m_CurrentIterator = returnSucccessors(
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
						public OutgoingReturnTransition<LETTER, STATE> next() {
							if (m_CurrentHier == null) {
								throw new NoSuchElementException();
							} else {
								OutgoingReturnTransition<LETTER, STATE> result = 
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
		
		public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
				final STATE hier) {
			return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
				/**
				 * Iterates over all OutgoingReturnTransition of state with 
				 * hierarchical successor hier. 
				 * Iterates over all outgoing return letters and uses the 
				 * iterators returned by returnSuccecessors(state, hier, letter)
				 */
				@Override
				public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
					Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
							new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
						Iterator<LETTER> m_LetterIterator;
						LETTER m_CurrentLetter;
						Iterator<OutgoingReturnTransition<LETTER, STATE>> m_CurrentIterator;
						{
							m_LetterIterator = lettersReturn().iterator();
							nextLetter();
						}
	
						private void nextLetter() {
							if (m_LetterIterator.hasNext()) {
								do {
									m_CurrentLetter = m_LetterIterator.next();
									m_CurrentIterator = returnSucccessors(
											hier, m_CurrentLetter).iterator();
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
						public OutgoingReturnTransition<LETTER, STATE> next() {
							if (m_CurrentLetter == null) {
								throw new NoSuchElementException();
							} else {
								OutgoingReturnTransition<LETTER, STATE> result = 
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
		
		
		public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
				) {
			return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
				/**
				 * Iterates over all OutgoingReturnTransition of state.
				 * Iterates over all outgoing return letters and uses the 
				 * iterators returned by returnSuccessors(state, letter)
				 */
				@Override
				public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
					Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
							new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
						Iterator<LETTER> m_LetterIterator;
						LETTER m_CurrentLetter;
						Iterator<OutgoingReturnTransition<LETTER, STATE>> m_CurrentIterator;
						{
							m_LetterIterator = lettersReturn().iterator();
							nextLetter();
						}
	
						private void nextLetter() {
							if (m_LetterIterator.hasNext()) {
								do {
									m_CurrentLetter = m_LetterIterator.next();
									m_CurrentIterator = returnSuccessors(m_CurrentLetter).iterator();
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
						public OutgoingReturnTransition<LETTER, STATE> next() {
							if (m_CurrentLetter == null) {
								throw new NoSuchElementException();
							} else {
								OutgoingReturnTransition<LETTER, STATE> result = 
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
		
		
		private boolean containsInternalTransition(LETTER letter, STATE succ) {
			Map<LETTER, Set<STATE>> map = m_InternalOut;
			if (map == null) {
				return false;
			}
			Set<STATE> result = map.get(letter);
			return result == null ? false : result.contains(succ);
		}
		
		private boolean containsCallTransition(LETTER letter, STATE succ) {
			Map<LETTER, Set<STATE>> map = m_CallOut;
			if (map == null) {
				return false;
			}
			Set<STATE> result = map.get(letter);
			return result == null ? false : result.contains(succ);
		}
		
		private boolean containsReturnTransition(STATE hier, LETTER letter, STATE succ) {
			Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnOut;
			if (map == null) {
				return false;
			}
			Map<STATE, Set<STATE>> hier2succs = map.get(letter);
			if (hier2succs == null) {
				return false;
			}
			Set<STATE> result = hier2succs.get(hier);
			return result == null ? false : result.contains(succ);
		}
	}
	
	private boolean containsInternalTransition(STATE state, LETTER letter, STATE succ) {
		return m_States.get(state).containsInternalTransition(letter, succ);
	}
	
	private boolean containsCallTransition(STATE state, LETTER letter, STATE succ) {
		return m_States.get(state).containsCallTransition(letter, succ);
	}
	
	private boolean containsReturnTransition(STATE state, STATE hier, LETTER letter, STATE succ) {
		return m_States.get(state).containsReturnTransition(hier, letter, succ);
	}
	
	private boolean checkTransitionsReturnedConsistent() {
		boolean result = true;
		for (STATE state : getStates()) {
			for (IncomingInternalTransition<LETTER, STATE> inTrans : internalPredecessors(state)) {
				result &= containsInternalTransition(inTrans.getPred(), inTrans.getLetter(), state);
				assert result;
			}
			for (OutgoingInternalTransition<LETTER, STATE> outTrans : internalSuccessors(state)) {
				result &= containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert result;
			}
			for (IncomingCallTransition<LETTER, STATE> inTrans : callPredecessors(state)) {
				result &= containsCallTransition(inTrans.getPred(), inTrans.getLetter(), state);
				assert result;
			}
			for (OutgoingCallTransition<LETTER, STATE> outTrans : callSuccessors(state)) {
				result &= containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert result;
			}
			for (IncomingReturnTransition<LETTER, STATE> inTrans : returnPredecessors(state)) {
				result &= containsReturnTransition(inTrans.getLinPred(), inTrans.getHierPred(), inTrans.getLetter(), state);
				assert result;
			}
			for (OutgoingReturnTransition<LETTER, STATE> outTrans : returnSuccessors(state)) {
				result &= containsReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());
				assert result;
			}
		}

		return result;
	}
	
	private boolean cecSumConsistent() {
		int sum = 0;
		for (CommonEntriesComponent cec : m_AllCECs) {
			sum += cec.m_Size;
		}
		int allStates = m_States.keySet().size();
		return sum == allStates;
	}
	
	private boolean allStatesAreInTheirCec() {
		boolean result = true;
		for (STATE state : m_States.keySet()) {
			StateContainer sc = m_States.get(state);
			CommonEntriesComponent cec = sc.getCommonEntriesComponent();
			if (!cec.m_BorderOut.keySet().contains(state)) {
				Set<STATE> empty = new HashSet<STATE>();
				result &= internalOutSummaryOutInCecOrForeigners(state, empty, cec);
			}
		}
		return result;
	}
	
	private boolean occuringStatesAreConsistent(CommonEntriesComponent cec) {
		boolean result = true;
		Set<STATE> downStates = cec.m_DownStates;
		Set<Entry> entries = cec.m_Entries;
		result &= downStatesAreCallPredsOfEntries(downStates, entries);
		assert (result);
		result &= eachStateHasThisCec(cec.getReturnOutCandidates(), cec);
		assert (result);
		for (STATE resident : cec.m_BorderOut.keySet()) {
			Set<STATE> foreigners = cec.m_BorderOut.get(resident);
			result &= internalOutSummaryOutInCecOrForeigners(resident, foreigners, cec);
			assert (result);
		}
		return result;
	}
	
	private boolean internalOutSummaryOutInCecOrForeigners(STATE state, Set<STATE> foreigners, CommonEntriesComponent cec) {
		StateContainer sc = m_States.get(state);
		Set<STATE> neighbors = new HashSet<STATE>();
		
		for (OutgoingInternalTransition<LETTER, STATE> trans : sc.internalSuccessors()) {
			STATE succ = trans.getSucc();
			StateContainer succSc = m_States.get(succ);
			if (succSc.getCommonEntriesComponent() == cec) {
				// do nothing
			} else {
				neighbors.add(succ);
			}
		}
		if (m_Summaries.containsKey(state)) {
			for (STATE succ : m_Summaries.get(state)) {
				StateContainer succSc = m_States.get(succ);
				if (succSc.getCommonEntriesComponent() == cec) {
					// do nothing
				} else {
					neighbors.add(succ);
				}
			}
		}
		boolean allNeighborAreForeigners = isSubset(neighbors, foreigners);
		boolean allForeignersAreNeighbor = isSubset(foreigners, neighbors);
		return allNeighborAreForeigners && allForeignersAreNeighbor;
	}
	
	private boolean eachStateHasThisCec(Set<STATE> states, CommonEntriesComponent cec) {
		boolean result = true;
		for (STATE state : states) {
			StateContainer sc = m_States.get(state);
			if (sc.getCommonEntriesComponent() != cec) {
				result = false;
			}
		}
		return result;
	}
	
	private boolean downStatesAreCallPredsOfEntries(Set<STATE> downStates, Set<Entry> entries) {
		Set<STATE> callPreds = new HashSet<STATE>();
		for (Entry entry : entries) {
			STATE entryState = entry.getState();
			if (isInitial(entryState)) {
				callPreds.add(getEmptyStackState());
			}
			for (IncomingCallTransition<LETTER, STATE> trans : callPredecessors(entryState)) {
				callPreds.add(trans.getPred());
			}
		}
		boolean callPredsIndownStates = isSubset(callPreds, downStates);
		boolean downStatesInCallPreds = isSubset(downStates, callPreds);
		return callPredsIndownStates && downStatesInCallPreds;
	}



}
