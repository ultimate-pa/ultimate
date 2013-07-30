package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
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
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.TransitionConsitenceCheck;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval.UpDownEntry;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.StateContainer.DownStateProp;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class NestedWordAutomatonReachableStates<LETTER,STATE> implements INestedWordAutomatonOldApi<LETTER,STATE>, INestedWordAutomaton<LETTER,STATE>, IDoubleDeckerAutomaton<LETTER, STATE> {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_Operand;
	
	private final Set<LETTER> m_InternalAlphabet;
	private final Set<LETTER> m_CallAlphabet;
	private final Set<LETTER> m_ReturnAlphabet;
	
	protected final StateFactory<STATE> m_StateFactory;
	
	private final Set<STATE> m_initialStates = new HashSet<STATE>();
	private final Set<STATE> m_finalStates = new HashSet<STATE>();
	
	private final Map<STATE,StateContainer<LETTER,STATE>> m_States = 
			new HashMap<STATE,StateContainer<LETTER,STATE>>();
	
	public static enum ReachProp { REACHABLE, NODEADEND_AD, NODEADEND_SD, FINANC, LIVE_AD, LIVE_SD };
	

	

	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as 
	 * map HierPREs -> LETTERs -> LinPREs -> SUCCs
	 * 
	 */
	private Map<STATE,Map<LETTER,Map<STATE,Set<STATE>>>> m_ReturnSummary =
			new HashMap<STATE,Map<LETTER,Map<STATE,Set<STATE>>>>();

	
	


	private Map<StateContainer<LETTER,STATE>,Set<StateContainer<LETTER,STATE>>> m_Summaries = new HashMap<StateContainer<LETTER,STATE>,Set<StateContainer<LETTER,STATE>>>();

	private Set<LETTER> m_EmptySetOfLetters = new HashSet<LETTER>(0);

	private AncestorComputation m_WithOutDeadEnds;
	private AncestorComputation m_OnlyLiveStates;
	private AcceptingSummeariesComputation m_AcceptingSummaries;
	private StronglyConnectedComponents m_StronglyConnectedComponents;
	

	
	private void addSummary(StateContainer<LETTER,STATE> callPred, StateContainer<LETTER,STATE> returnSucc) {
		Set<StateContainer<LETTER,STATE>> returnSuccs = m_Summaries.get(callPred);
		if (returnSuccs == null) {
			returnSuccs = new HashSet<StateContainer<LETTER,STATE>>();
			m_Summaries.put(callPred, returnSuccs);
		}
		returnSuccs.add(returnSucc);
	}
	
	public NestedWordAutomatonReachableStates(INestedWordAutomatonSimple<LETTER,STATE> operand) throws OperationCanceledException {
		this.m_Operand = operand;
		m_InternalAlphabet = operand.getInternalAlphabet();
		m_CallAlphabet = operand.getCallAlphabet();
		m_ReturnAlphabet = operand.getReturnAlphabet();
		m_StateFactory = operand.getStateFactory();
		try {
			new ReachableStatesComputation();
//			computeDeadEnds();
//			new NonLiveStateComputation();
			computeStronglyConnectedComponents();
			getStronglyConnectedComponents().computeNestedLassoRuns(false);
			s_Logger.info(stateContainerInformation());
			assert (new TransitionConsitenceCheck<LETTER, STATE>(this)).consistentForAll();

			assert (checkTransitionsReturnedConsistent());

			
		} catch (Error e) {
			String message = "// Problem with  removeUnreachable";
			ResultChecker.writeToFileIfPreferred("FailedremoveUnreachable",
					message, operand);
			throw e;
		} catch (RuntimeException e) {
			String message = "// Problem with  removeUnreachable";
			ResultChecker.writeToFileIfPreferred("FailedremoveUnreachable",
					message, operand);
			throw e;
		}
	}
	
	private String stateContainerInformation() {
		int inMap = 0;
		int outMap = 0;
		for(STATE state : m_States.keySet()) {
			StateContainer<LETTER, STATE> cont = m_States.get(state);
			if (cont instanceof StateContainerFieldAndMap) {
				if (((StateContainerFieldAndMap<LETTER,STATE>) cont).mapModeIncoming()) {
					inMap++;
				}
				if (((StateContainerFieldAndMap<LETTER,STATE>) cont).mapModeOutgoing()) {
					outMap++;
				}
			}
		}
		return m_States.size() + " StateContainers " + inMap + " in inMapMode" + outMap + " in outMapMode";
	}
	
//	public boolean isDeadEnd(STATE state) {
//		ReachProp reachProp = m_States.get(state).getReachProp();
//		return  reachProp == ReachProp.REACHABLE;
//	}
	

	
	
	public AncestorComputation getWithOutDeadEnds() {
		return m_WithOutDeadEnds;
	}

	public AncestorComputation getOnlyLiveStates() {
		return m_OnlyLiveStates;
	}
	
	public StronglyConnectedComponents getStronglyConnectedComponents() {
		return m_StronglyConnectedComponents;
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
	public Set<LETTER> getAlphabet() {
		return m_InternalAlphabet;
	}

	@Override
	public String sizeInformation() {
		int states = m_States.size();
		return states + " states.";
	}

	@Override
	public Set<LETTER> getInternalAlphabet() {
		return m_InternalAlphabet;
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return m_CallAlphabet;
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
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
		return Collections.unmodifiableSet(m_initialStates);
	}

	@Override
	public Collection<STATE> getFinalStates() {
		return Collections.unmodifiableSet(m_finalStates);
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
	public STATE getEmptyStackState() {
		return m_Operand.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(STATE state) {
		return m_States.get(state).lettersInternal();
	}

	@Override
	public Set<LETTER> lettersCall(STATE state) {
		return m_States.get(state).lettersCall();
	}

	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		return m_States.get(state).lettersReturn();
	}

	@Override
	public Set<LETTER> lettersInternalIncoming(STATE state) {
		return m_States.get(state).lettersInternalIncoming();
	}

	@Override
	public Set<LETTER> lettersCallIncoming(STATE state) {
		return m_States.get(state).lettersCallIncoming();
	}

	@Override
	public Set<LETTER> lettersReturnIncoming(STATE state) {
		return m_States.get(state).lettersReturnIncoming();
	}

	@Override
	public Set<LETTER> lettersReturnSummary(STATE state) {
		if (!m_States.containsKey(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		 Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnSummary.get(state);
		return map == null ? new HashSet<LETTER>(0) : map.keySet();
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
	public boolean finalIsTrap() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isDeterministic() {
		return false;
	}

	@Override
	public boolean isTotal() {
		throw new UnsupportedOperationException();
	}
	
	private void addReturnSummary(STATE pred, STATE hier, LETTER letter, STATE succ) {
		Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = m_ReturnSummary.get(hier);
		if (letter2pred2succs == null) {
			letter2pred2succs = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
			m_ReturnSummary.put(hier, letter2pred2succs);
		}
		Map<STATE, Set<STATE>> pred2succs = letter2pred2succs.get(letter);
		if (pred2succs == null) {
			pred2succs = new HashMap<STATE, Set<STATE>>();
			letter2pred2succs.put(letter, pred2succs);
		}
		Set<STATE> succS = pred2succs.get(pred);
		if (succS == null) {
			succS = new HashSet<STATE>();
			pred2succs.put(pred, succS);
		}
		succS.add(succ);
	}
	
	
	public Collection<LETTER> lettersSummary(STATE hier) {
		Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnSummary.get(hier);
		return map == null ? m_EmptySetOfLetters  : map.keySet();
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> 
						returnSummarySuccessor(LETTER letter, STATE hier) {
		Set<SummaryReturnTransition<LETTER, STATE>> result = 
				new HashSet<SummaryReturnTransition<LETTER, STATE>>();
		Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succ = 
				m_ReturnSummary.get(hier);
		if (letter2pred2succ == null) {
			return result;
		}
		Map<STATE, Set<STATE>> pred2succ = letter2pred2succ.get(letter);
		if (pred2succ == null) {
			return result;
		}
		for (STATE pred : pred2succ.keySet()) {
			if (pred2succ.get(pred) != null) {
				for (STATE succ : pred2succ.get(pred)) {
				SummaryReturnTransition<LETTER, STATE> srt = 
					new SummaryReturnTransition<LETTER, STATE>(pred, letter, succ);
				result.add(srt);
				}
			}
		}
		return result;
	}
	
	


	public Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(final STATE hier) {
		return new Iterable<SummaryReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all SummaryReturnTransition of hier.
			 */
			@Override
			public Iterator<SummaryReturnTransition<LETTER, STATE>> iterator() {
				Iterator<SummaryReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<SummaryReturnTransition<LETTER, STATE>>() {
					Iterator<LETTER> m_LetterIterator;
					LETTER m_CurrentLetter;
					Iterator<SummaryReturnTransition<LETTER, STATE>> m_CurrentIterator;
					{
						m_LetterIterator = lettersSummary(hier).iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = returnSummarySuccessor(
										m_CurrentLetter, hier).iterator();
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
					public SummaryReturnTransition<LETTER, STATE> next() {
						if (m_CurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							SummaryReturnTransition<LETTER, STATE> result = 
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
		return m_States.get(succ).returnPredecessors(letter);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			STATE succ) {
		return m_States.get(succ).returnPredecessors();
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			STATE state, STATE hier, LETTER letter) {
		return m_States.get(state).returnSuccessors(hier, letter);
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
	
	
	public void computeDeadEnds() {
		if (m_WithOutDeadEnds != null) {
			return;
//			throw new AssertionError("dead are already computed");
		}
		HashSet<StateContainer<LETTER, STATE>> acceptings = 
				new HashSet<StateContainer<LETTER,STATE>>();
		for (STATE fin : getFinalStates()) {
			StateContainer<LETTER,STATE> cont = m_States.get(fin);
			assert cont.getReachProp() != ReachProp.NODEADEND_AD && cont.getReachProp() != ReachProp.NODEADEND_SD;
			acceptings.add(cont);
		}
		m_WithOutDeadEnds = new AncestorComputation(acceptings, 
				ReachProp.NODEADEND_AD, ReachProp.NODEADEND_SD, DownStateProp.REACH_FINAL_ONCE);
	}
	
	public void computeStronglyConnectedComponents() {
		if (m_StronglyConnectedComponents != null) {
			throw new AssertionError("SCCs are already computed");
		}
		assert m_AcceptingSummaries == null;
		m_AcceptingSummaries = new AcceptingSummeariesComputation();
		m_StronglyConnectedComponents = new StronglyConnectedComponents(m_AcceptingSummaries);
	}
	
	public void computeNonLiveStates() {
		if (m_OnlyLiveStates != null) {
			return;
//			throw new AssertionError("non-live states are already computed");
		}
		if (getStronglyConnectedComponents() == null) {
			computeStronglyConnectedComponents();
		}

		HashSet<StateContainer<LETTER, STATE>> nonLiveStartingSet = 
				new HashSet<StateContainer<LETTER,STATE>>(m_StronglyConnectedComponents.getStatesOfAllSCCs());
		m_OnlyLiveStates = new AncestorComputation(nonLiveStartingSet, 
				ReachProp.LIVE_AD, ReachProp.LIVE_SD, DownStateProp.REACH_FINAL_INFTY);
	}
	
	

	public Set<STATE> getDownStates(STATE state) {
		StateContainer<LETTER, STATE> cont = m_States.get(state);
		return cont.getDownStates().keySet();
	}
	
	public boolean isDoubleDecker(STATE up, STATE down) {
		return getDownStates(up).contains(down);
	}
	

	
	
	
	////////////////////////////////////////////////////////////////////////////
	
	private class ReachableStatesComputation {
		private int m_NumberOfConstructedStates = 0;
		private final LinkedList<StateContainer<LETTER,STATE>> m_ForwardWorklist = 
				new LinkedList<StateContainer<LETTER,STATE>>();
		private final LinkedList<StateContainer<LETTER,STATE>> m_DownPropagationWorklist =
				new LinkedList<StateContainer<LETTER,STATE>>();
		
		
//		/**
//		 * Contains states that are in the worklist or processed at the moment.
//		 * Used to avoid insertion of elements to doubleDecker worklist whose
//		 * up state will be processed anyway.
//		 */
//		private final Set<STATE> m_WorklistAndCurrentState = 
//				new HashSet<STATE>();

		ReachableStatesComputation() throws OperationCanceledException {
			addInitialStates(m_Operand.getInitialStates());

			do {
				while (!m_ForwardWorklist.isEmpty()) {
					StateContainer<LETTER,STATE> cont = m_ForwardWorklist.remove(0);
					cont.eraseUnpropagatedDownStates();
					Set<STATE> newDownStatesFormSelfloops = null;
					
					if (candidateForOutgoingReturn(cont.getState())) {
						for (STATE down : cont.getDownStates().keySet()) {
							if (down != getEmptyStackState()) {
								Set<STATE> newDownStates = 
										addReturnsAndSuccessors(cont, down);
								if (newDownStates != null) {
									if (newDownStatesFormSelfloops == null) {
										newDownStatesFormSelfloops = new HashSet<STATE>();
									}
									newDownStatesFormSelfloops.addAll(newDownStates);
								}
							}
						}
					}

					addInternalsAndSuccessors(cont);
					{
						Set<STATE> newDownStates = addCallsAndSuccessors(cont);
						if (newDownStates != null) {
							if (newDownStatesFormSelfloops == null) {
								newDownStatesFormSelfloops = new HashSet<STATE>();
							}
							newDownStatesFormSelfloops.addAll(newDownStates);
						}
					}
					
					if (newDownStatesFormSelfloops != null) {
						assert !newDownStatesFormSelfloops.isEmpty();
						for (STATE down : newDownStatesFormSelfloops) {
							cont.addReachableDownState(down);
						}
						m_DownPropagationWorklist.add(cont);
					}

					if (!UltimateServices.getInstance().continueProcessing()) {
						throw new OperationCanceledException();
					}
				}
				
				while(m_ForwardWorklist.isEmpty() && !m_DownPropagationWorklist.isEmpty()) {
					StateContainer<LETTER,STATE> cont = 
							m_DownPropagationWorklist.remove(0);
					propagateNewDownStates(cont);
				}
				
				
			} while (!m_DownPropagationWorklist.isEmpty() || !m_ForwardWorklist.isEmpty());
			assert (m_ForwardWorklist.isEmpty());
			assert (m_DownPropagationWorklist.isEmpty());
			assert checkTransitionsReturnedConsistent();
			
			
			//TODO: This is a test for constructRun
			for (STATE fin : getFinalStates()) {
				NestedRun<LETTER,STATE> run = constructRun(m_States.get(fin));
				assert (new Accepts<LETTER, STATE>(NestedWordAutomatonReachableStates.this, run.getWord())).getResult();
			}
		}
		
		
		private void addInitialStates(Iterable<STATE> initialStates) {
			for (STATE state : initialStates) {
				m_initialStates.add(state);
				HashMap<STATE, Integer> downStates = new HashMap<STATE,Integer>();
				downStates.put(getEmptyStackState(), 0);
				StateContainer<LETTER,STATE> sc = addState(state, downStates);
				m_States.put(state, sc);
			}
		}
		
		
		
		/**
		 * Construct State Container. Add to CommonEntriesComponent<LETTER,STATE>. Add to
		 * ForwardWorklist.
		 * @param state
		 * @param cec
		 * @return
		 */
		private StateContainer<LETTER, STATE> addState(STATE state, HashMap<STATE,Integer> downStates) {
			assert !m_States.containsKey(state);
			if (m_Operand.isFinal(state)) {
				m_finalStates.add(state);
			}
			boolean canHaveOutgoingReturn = candidateForOutgoingReturn(state);
			StateContainer<LETTER,STATE> result = 
					new StateContainerFieldAndMap<LETTER,STATE>(state, 
					m_NumberOfConstructedStates, downStates, canHaveOutgoingReturn);
			m_NumberOfConstructedStates++;
			m_States.put(state, result);
			m_ForwardWorklist.add(result);
			return result;
		}
		
		private boolean candidateForOutgoingReturn(STATE state) {
			return !m_Operand.lettersReturn(state).isEmpty();
//			return true;
		}
		

		private <E> Set<E> differenceSet(Set<E> minuend, Set<E> subtrahend) {
			Set<E> result = new HashSet<E>();
			for (E elem : minuend) {
				if (!subtrahend.contains(elem)) {
					result.add(elem);
				}
			}
			return result;
		}
		
		private void addInternalsAndSuccessors(StateContainer<LETTER,STATE> cont) {
			STATE state = cont.getState();
			for (OutgoingInternalTransition<LETTER, STATE> trans : 
											m_Operand.internalSuccessors(state)) {
				STATE succ = trans.getSucc();
				StateContainer<LETTER,STATE> succSC = m_States.get(succ);
				if (succSC == null) {
					succSC = addState(succ, new HashMap<STATE, Integer>(cont.getDownStates()));
				} else {
					addNewDownStates(cont, succSC, cont.getDownStates().keySet());
				}
				assert (!containsCallTransition(state, trans.getLetter(), succ));
				cont.addInternalOutgoing(trans);
				succSC.addInternalIncoming(new IncomingInternalTransition<LETTER, STATE>(state, trans.getLetter()));
			}
		}
		
		



		private Set<STATE> addCallsAndSuccessors(StateContainer<LETTER,STATE> cont) {
			boolean addedSelfloop = false;
			STATE state = cont.getState();
			for (OutgoingCallTransition<LETTER, STATE> trans : 
										m_Operand.callSuccessors(cont.getState())) {
				STATE succ = trans.getSucc();
				StateContainer<LETTER,STATE> succCont = m_States.get(succ);
				HashMap<STATE, Integer> succDownStates = new HashMap<STATE,Integer>();
				succDownStates.put(cont.getState(), 0);
				if (succCont == null) {
					succCont = addState(succ, succDownStates);
				} else {
					addNewDownStates(cont, succCont, succDownStates.keySet());
					if (cont == succCont) {
						addedSelfloop = true;
					}
				}
				assert (!containsCallTransition(state, trans.getLetter(), succ));
				cont.addCallOutgoing(trans);
				succCont.addCallIncoming(
						new IncomingCallTransition<LETTER, STATE>(state, trans.getLetter()));
			}
			if (addedSelfloop) {
				HashSet<STATE> newDownStates = new HashSet<STATE>(1);
				newDownStates.add(state);
				return newDownStatesSelfloop(cont, newDownStates);
			} else {
				return null;
			}

		}
		
		

		private Set<STATE> addReturnsAndSuccessors(StateContainer<LETTER,STATE> cont, STATE down) {
			boolean addedSelfloop = false;
			STATE state = cont.getState();
			StateContainer<LETTER,STATE> downCont = null;
			for (OutgoingReturnTransition<LETTER, STATE> trans : 
									m_Operand.returnSuccessorsGivenHier(state,down)) {
				assert (down.equals(trans.getHierPred()));
				if (downCont == null) {
					downCont = m_States.get(down);
				}
				STATE succ = trans.getSucc();
				StateContainer<LETTER,STATE> succCont = m_States.get(succ);
				if (succCont == null) {
					succCont = addState(succ, new HashMap<STATE, Integer>(downCont.getDownStates()));
				} else {
					addNewDownStates(cont, succCont, downCont.getDownStates().keySet());
					if (cont == succCont) {
						addedSelfloop = true;
					}
				}
				assert (!containsReturnTransition(state, down, trans.getLetter(), succ));
				cont.addReturnOutgoing(trans);
				succCont.addReturnIncoming(
						new IncomingReturnTransition<LETTER, STATE>(cont.getState(), down, trans.getLetter()));
				addReturnSummary(state, down, trans.getLetter(), succ);
				addSummary(downCont, succCont);
			}
			if (addedSelfloop) {
				return newDownStatesSelfloop(cont, downCont.getDownStates().keySet());
			} else {
				return null;
			}
		}


		/**
		 * @param cont
		 * @param newDownStatesSelfloop
		 * @param downCont
		 * @return
		 */
		private Set<STATE> newDownStatesSelfloop(StateContainer<LETTER, STATE> cont,
				Set<STATE> propagatedDownStates) {
			Set<STATE> newDownStates = null;
			for (STATE downs : propagatedDownStates) {
				if (!cont.getDownStates().keySet().contains(downs)) {
					if (newDownStates == null) {
						newDownStates = new HashSet<STATE>();
					}
					newDownStates.add(downs);
				}
				
			}
			return newDownStates;
		}

		
		private void addNewDownStates(StateContainer<LETTER, STATE> cont,
				StateContainer<LETTER, STATE> succCont,
				Set<STATE> potentiallyNewDownStates) {
			if (cont == succCont) {
				return;
			} else {
				boolean newDownStateWasPropagated = false;
				for (STATE down : potentiallyNewDownStates) {
					boolean newlyAdded = succCont.addReachableDownState(down);
					if (newlyAdded) {
						newDownStateWasPropagated = true;
					}
				}
				if (newDownStateWasPropagated) {
					m_DownPropagationWorklist.add(succCont);
				}
			}
		}


		private void propagateNewDownStates(StateContainer<LETTER, STATE> cont) {
			Set<STATE> unpropagatedDownStates = cont.getUnpropagatedDownStates();
			if (unpropagatedDownStates  == null) {
				return;
			}
			for (OutgoingInternalTransition<LETTER, STATE> trans : cont.internalSuccessors()) {
				StateContainer<LETTER, STATE> succCont = m_States.get(trans.getSucc());
				addNewDownStates(cont, succCont, unpropagatedDownStates);
			}
			for (SummaryReturnTransition<LETTER, STATE> trans : returnSummarySuccessor(cont.getState())) {
				StateContainer<LETTER, STATE> succCont = m_States.get(trans.getSucc());
				addNewDownStates(cont, succCont, unpropagatedDownStates);
			}
			if(candidateForOutgoingReturn(cont.getState())) {
				HashSet<STATE> newDownStatesFormSelfloops = null;
				for (STATE down : cont.getUnpropagatedDownStates()) {
					if (down != getEmptyStackState()) {
						Set<STATE> newDownStates = 
								addReturnsAndSuccessors(cont, down);
						if (newDownStates != null) {
							if (newDownStatesFormSelfloops == null) {
								newDownStatesFormSelfloops = new HashSet<STATE>();
							}
							newDownStatesFormSelfloops.addAll(newDownStates);
						}
					}
				}
				cont.eraseUnpropagatedDownStates();
				if (newDownStatesFormSelfloops != null) {
					assert !newDownStatesFormSelfloops.isEmpty();
					for (STATE down : newDownStatesFormSelfloops) {
						cont.addReachableDownState(down);
					}
					m_DownPropagationWorklist.add(cont);
				}
			} else {
				cont.eraseUnpropagatedDownStates();
			}
			
		}
	}

		

	
	

////////////////////////////////////////////////////////////////////////////////
	public class AncestorComputation {
		
		private final ReachProp m_rpAllDown;
		private final ReachProp m_rpSomeDown;
		private final DownStateProp m_DownStateProp;
		
		
		private final Set<STATE> m_Ancestors = new HashSet<STATE>();
		private final Set<STATE> m_AncestorsInitial = new HashSet<STATE>();
		private final Set<STATE> m_AncestorsAccepting = new HashSet<STATE>();
		
		private ArrayDeque<StateContainer<LETTER,STATE>> m_NonReturnBackwardWorklist =
				new ArrayDeque<StateContainer<LETTER,STATE>>();
		private Set<StateContainer<LETTER,STATE>> m_HasIncomingReturn = 
				new HashSet<StateContainer<LETTER,STATE>>();
		private ArrayDeque<StateContainer<LETTER,STATE>> m_PropagationWorklist =
				new ArrayDeque<StateContainer<LETTER,STATE>>();

		
		
		public Set<STATE> getStates() {
			return m_Ancestors;
		}


		public Set<STATE> getInitials() {
			return m_AncestorsInitial;
		}


		public Set<STATE> getFinals() {
			return m_AncestorsAccepting;
		}


		AncestorComputation(HashSet<StateContainer<LETTER,STATE>> startSet, 
				ReachProp allDown, ReachProp someDown, DownStateProp downStateProp) {
			m_rpAllDown = allDown;
			m_rpSomeDown = someDown;
			m_DownStateProp = downStateProp;
			
			for (StateContainer<LETTER,STATE> cont : startSet) {
				cont.setReachProp(m_rpAllDown);
				m_Ancestors.add(cont.getState());
				m_NonReturnBackwardWorklist.add(cont);
			}

			while (!m_NonReturnBackwardWorklist.isEmpty()) {
				StateContainer<LETTER,STATE> cont = m_NonReturnBackwardWorklist.removeFirst();
				if (m_initialStates.contains(cont.getState())) {
					m_AncestorsInitial.add(cont.getState());
				}
				if (isFinal(cont.getState())) {
					m_AncestorsAccepting.add(cont.getState());
				}
				
				for (IncomingInternalTransition<LETTER, STATE> inTrans : cont
						.internalPredecessors()) {
					STATE pred = inTrans.getPred();
					StateContainer<LETTER,STATE> predCont = m_States.get(pred);
					if (predCont.getReachProp() != m_rpAllDown) {
						predCont.setReachProp(m_rpAllDown);
						m_Ancestors.add(pred);
						m_NonReturnBackwardWorklist.add(predCont);
					}
				}
				for (IncomingReturnTransition<LETTER, STATE> inTrans : cont
						.returnPredecessors()) {
					STATE hier = inTrans.getHierPred();
					StateContainer<LETTER,STATE> hierCont = m_States.get(hier);
					if (hierCont.getReachProp() != m_rpAllDown) {
						hierCont.setReachProp(m_rpAllDown);
						m_Ancestors.add(hier);
						m_NonReturnBackwardWorklist.add(hierCont);
					}
					m_HasIncomingReturn.add(cont);
				}
				for (IncomingCallTransition<LETTER, STATE> inTrans : cont
						.callPredecessors()) {
					STATE pred = inTrans.getPred();
					StateContainer<LETTER,STATE> predCont = m_States.get(pred);
					if (predCont.getReachProp() != m_rpAllDown) {
						predCont.setReachProp(m_rpAllDown);
						m_Ancestors.add(pred);
						m_NonReturnBackwardWorklist.add(predCont);
					}
				}
			}
			
			for (StateContainer<LETTER,STATE> cont : m_HasIncomingReturn) {
				for (IncomingReturnTransition<LETTER, STATE> inTrans : cont
						.returnPredecessors()) {
					STATE lin = inTrans.getLinPred();
					StateContainer<LETTER,STATE> linCont = m_States.get(lin);
					if (linCont.getReachProp() != m_rpAllDown) {
						Set<STATE> potentiallyNewDownStates = new HashSet<STATE>(1);
						potentiallyNewDownStates.add(inTrans.getHierPred());
						addNewDownStates(null, linCont, potentiallyNewDownStates);
//						if (linCont.getUnpropagatedDownStates() == null) {
//							assert !m_PropagationWorklist.contains(linCont);
//							m_PropagationWorklist.addLast(linCont);
//						}
//						ReachProp oldValue = linCont.modifyDownProp(inTrans.getHierPred(),m_rpSomeDown);
//						assert oldValue != m_rpAllDown;
					}
				}
			}
			
			while (!m_PropagationWorklist.isEmpty()) {
				StateContainer<LETTER,STATE> cont = m_PropagationWorklist.removeFirst();
				propagateBackward(cont);
			}
			removeUnnecessaryInitialStates();
		}
		
		
		private void removeUnnecessaryInitialStates() {
			Iterator<STATE> it = m_AncestorsInitial.iterator();
			while (it.hasNext()) {
				STATE state = it.next();
				StateContainer<LETTER, STATE> cont = m_States.get(state);
				if (cont.getReachProp() == m_rpAllDown) {
					continue;
				} else {
					boolean reachFinalOnce = cont.hasDownProp(
							getEmptyStackState(), DownStateProp.REACH_FINAL_ONCE); 
					if (reachFinalOnce) {
						continue;
					} else {
						it.remove();
					}
				}
			}
		}

		private void propagateBackward(StateContainer<LETTER, STATE> cont) {
			Set<STATE> unpropagatedDownStates = cont.getUnpropagatedDownStates();
			cont.eraseUnpropagatedDownStates();
			Set<STATE> newUnpropagatedDownStatesSelfloop = null;
			for (IncomingInternalTransition<LETTER, STATE> inTrans : cont
					.internalPredecessors()) {
				STATE pred = inTrans.getPred();
				StateContainer<LETTER,STATE> predCont = m_States.get(pred);
				if (predCont.getReachProp() != m_rpAllDown) {
					addNewDownStates(cont, predCont, unpropagatedDownStates);
				}
			}
			for (IncomingReturnTransition<LETTER, STATE> inTrans : cont
					.returnPredecessors()) {
				STATE hier = inTrans.getHierPred();
				StateContainer<LETTER,STATE> hierCont = m_States.get(hier);
				if (hierCont.getReachProp() != m_rpAllDown) {
					addNewDownStates(cont, hierCont, unpropagatedDownStates);
				}
				STATE lin = inTrans.getLinPred();
				StateContainer<LETTER,STATE> linCont = m_States.get(lin);
				if (linCont.getReachProp() != m_rpAllDown) {
					if (atLeastOneOccursAsDownState(hierCont, unpropagatedDownStates)) {
						if (linCont == cont) {
							boolean hierAlreadyPropagated = cont.hasDownProp(hier, m_DownStateProp);
							if (!hierAlreadyPropagated) {
								if (newUnpropagatedDownStatesSelfloop == null) {
									newUnpropagatedDownStatesSelfloop = new HashSet<STATE>();
								}
								newUnpropagatedDownStatesSelfloop.add(hier);
							}
						} else {
							HashSet<STATE> potentiallyNewDownState = new HashSet<STATE>(1);
							potentiallyNewDownState.add(hier);
							addNewDownStates(cont, linCont, potentiallyNewDownState);
						}
					}

				}
			}
			if (newUnpropagatedDownStatesSelfloop != null) {
				for (STATE down : newUnpropagatedDownStatesSelfloop) {
					cont.setDownProp(down, m_DownStateProp);
				}
				assert !m_PropagationWorklist.contains(cont);
				m_PropagationWorklist.add(cont);
			}
		}
		
	
		private boolean atLeastOneOccursAsDownState(
				StateContainer<LETTER, STATE> hierCont,
				Set<STATE> unpropagatedDownStates) {
			for (STATE state : unpropagatedDownStates) {
				if (hierCont.getDownStates().containsKey(state)) {
					return true;
				}
			}
			return false;
		}

		private void addNewDownStates(StateContainer<LETTER, STATE> cont,
				StateContainer<LETTER, STATE> predCont,
				Set<STATE> potentiallyNewDownStates) {
			if (cont == predCont) {
				return ;
			} else {
				boolean isAlreadyInWorklist = 
						(predCont.getUnpropagatedDownStates() != null);
				assert (isAlreadyInWorklist == m_PropagationWorklist.contains(predCont));
				assert (!isAlreadyInWorklist || predCont.getReachProp() == m_rpSomeDown);
				boolean newDownStateWasPropagated = false;
				for (STATE down : potentiallyNewDownStates) {
					if (predCont.getDownStates().containsKey(down)) {
						boolean modified = predCont.setDownProp(down, m_DownStateProp);
						if (modified) {
							newDownStateWasPropagated = true;
						}
						
					}
				}
				if (newDownStateWasPropagated) {
					if (!isAlreadyInWorklist) {
						assert !m_PropagationWorklist.contains(predCont);
						m_PropagationWorklist.add(predCont);
					}
					if (predCont.getReachProp() != m_rpSomeDown) {
						assert predCont.getReachProp() != m_rpAllDown;
						predCont.setReachProp(m_rpSomeDown);
						assert !m_Ancestors.contains(predCont.getState());
						m_Ancestors.add(predCont.getState());
					}
				}
			}
		}
		
		
		/**
		 * Return true iff the DoubleDecker (up,down) is reachable in the 
		 * original automaton (before removal of deadEnds or non-live states).
		 * This is a workaround to maintain backward compatibility with the old
		 * implementation. In the future we return true if (up,down) is 
		 * reachable in the resulting automaton 
		 */
		public boolean isDownState(STATE up, STATE down) {
			StateContainer<LETTER, STATE> cont = m_States.get(up);
			assert (cont.getReachProp() == m_rpAllDown || cont.getReachProp() == m_rpSomeDown);
			return cont.getDownStates().containsKey(down);
//			if (cont.getReachProp() == ReachProp.NODEADEND_AD) {
//				assert (cont.getDownStates().containsKey(down));
//				return true;
//			} else {
//				assert cont.getReachProp() == m_rpSomeDown;
//				ReachProp reach = cont.getDownStates().get(up);
//				if (reach == m_rpSomeDown) {
//					return true;
//				} else {
//					return false;
//				}
//			}
		}
		

		/**
		 * Returns the set of all down states such that (up,down) is reachable
		 * DoubleDecker in original automaton (before removal of deadEnds or 
		 * non-live states).
		 * This is a workaround to maintain backward compatibility with the old
		 * implementation. In the future we return set of down states in 
		 * resulting automaton.
		 */
		public Set<STATE> getDownStates(STATE state) {
			Set<STATE> downStates;
			StateContainer<LETTER, STATE> cont = m_States.get(state);
//			if (cont.getReachProp() == ReachProp.NODEADEND_AD) {
				downStates = cont.getDownStates().keySet();
//			} else {
//				assert cont.getReachProp() == ReachProp.NODEADEND_SD;
//				downStates = new HashSet<STATE>();
//				for (Entry<STATE, ReachProp> down : cont.getDownStates().entrySet()) {
//					if (down.getValue() == ReachProp.NODEADEND_SD) {
//						downStates.add(down.getKey());
//					} else {
//						assert down.getValue() == ReachProp.REACHABLE;
//					}
//				}
//			}
//			for(Entry<LETTER,STATE> entry : m_States.get(up).getCommonEntriesComponent().getEntries()) {
//				STATE entryState = entry.getState();
//				for (IncomingCallTransition<LETTER, STATE> trans : callPredecessors(entryState)) {
//					STATE callPred = trans.getPred();
//					StateContainer<LETTER, STATE> callPredCont = m_States.get(callPred);
//					if (callPredCont.getReachProp() != ReachProp.REACHABLE) {
//						downStates.add(callPred);
//					}
//				}
//				if (m_initialStatesAfterDeadEndRemoval.contains(entryState)) {
//					downStates.add(getEmptyStackState());
//				}
//			}
			return downStates;
		}
		
		
		/**
		 * Return true if the DoubleDecker (state,auxiliaryEmptyStackState) can
		 * reach a state in the TargetSet (finals DeadEndComputation, accepting
		 * SSCs in non-live computation)
		 */
		public boolean isInitial(STATE state) {
			if (!m_initialStates.contains(state)) {
				throw new IllegalArgumentException("Not initial state");
			}
			StateContainer<LETTER, STATE> cont = m_States.get(state);
			if (cont.getReachProp() == m_rpAllDown) {
//				assert cont.getDownStates().get(getEmptyStackState()) == ReachProp.REACHABLE;
				return true;
			} else {
				if (cont.hasDownProp(getEmptyStackState(),m_DownStateProp)) {
					return true;
				} else {
					return false;
				}
			}
		}
		
		
		/**
		 * returns all triples (up,down,entry) such that from the DoubleDecker
		 * (up,down) the starting states of this ancestor computation (e.g., 
		 * final states in dead end computation) is reachalbe.
		 * This is a workaround to maintain backward compatibility. In the 
		 * future we return triples reachable in resulting automaton.
		 * @return
		 */
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
						private StateContainer<LETTER, STATE> m_StateContainer;

						{
							m_UpIterator = m_States.keySet().iterator();
							if (m_UpIterator.hasNext()) {
								m_Up = m_UpIterator.next();
								m_StateContainer = m_States.get(m_Up);
								m_DownIterator = m_StateContainer.getDownStates().keySet().iterator();
							} else {
								m_hasNext = false;
							}
							computeNextElement();
							
						}
						
						private void computeNextElement() {
							m_Down = null;
							while (m_Down == null && m_hasNext) {
								if (m_StateContainer.getReachProp() != m_rpAllDown && m_DownIterator.hasNext()) {
									STATE downCandidate = m_DownIterator.next();
									if (m_StateContainer.getReachProp() == ReachProp.REACHABLE) {
										m_Down = downCandidate;
									} else {
										assert m_StateContainer.getReachProp() == m_rpSomeDown;
										if (!m_StateContainer.hasDownProp(downCandidate, m_DownStateProp)) {
											m_Down = downCandidate;
										}
									}
								} else {
									if (m_UpIterator.hasNext()) {
										m_Up = m_UpIterator.next();
										m_StateContainer = m_States.get(m_Up);
										m_DownIterator = m_StateContainer.getDownStates().keySet().iterator();
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
								assert m_Down == getEmptyStackState();
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
					if (state != getEmptyStackState()) {
						for (LETTER letter : lettersCall(state)) {
							for (STATE succ : succCall(state, letter)) {
								callSuccs.add(succ);
							}
						}
					}
					return callSuccs;
				}
				
				
			};

		}

	}
	
	


	////////////////////////////////////////////////////////////////////////////
	
	private class AcceptingSummeariesComputation {
		private final ArrayDeque<StateContainer<LETTER,STATE>> m_FinAncWorklist =
				new ArrayDeque<StateContainer<LETTER,STATE>>();
		private final Map<StateContainer<LETTER, STATE>, Set<StateContainer<LETTER, STATE>>> m_AcceptingSummaries = 
				new HashMap<StateContainer<LETTER, STATE>, Set<StateContainer<LETTER, STATE>>>();

		
		public AcceptingSummeariesComputation() {
			init();
			while (!m_FinAncWorklist.isEmpty()) {
				StateContainer<LETTER, STATE> cont = m_FinAncWorklist.removeFirst();
				propagateNewDownStates(cont);
			}
		}
		
		
		public Map<StateContainer<LETTER, STATE>, Set<StateContainer<LETTER, STATE>>> getAcceptingSummaries() {
			return m_AcceptingSummaries;
		}
		
		private void init() {
			for (STATE fin : m_finalStates) {
				StateContainer<LETTER, STATE> cont = m_States.get(fin);
				addNewDownStates(null, cont, cont.getDownStates().keySet());
			}
		}
		
		
		private void addNewDownStates(StateContainer<LETTER, STATE> cont,
				StateContainer<LETTER, STATE> succCont,
				Set<STATE> potentiallyNewDownStates) {
			if (cont == succCont) {
				return;
			} else {
				boolean newDownStateWasPropagated = false;
				for (STATE down : potentiallyNewDownStates) {
					boolean modified = succCont.setDownProp(down, DownStateProp.REACHABLE_FROM_FINAL_WITHOUT_CALL);
					if (modified) {
						newDownStateWasPropagated = true;
					}
				}
				if (newDownStateWasPropagated) {
					m_FinAncWorklist.add(succCont);
				}
			}
		}

		
		private void propagateNewDownStates(StateContainer<LETTER, STATE> cont) {
			Set<STATE> unpropagatedDownStates = cont.getUnpropagatedDownStates();
			if (unpropagatedDownStates  == null) {
				return;
			}
			for (OutgoingInternalTransition<LETTER, STATE> trans : cont.internalSuccessors()) {
				StateContainer<LETTER, STATE> succCont = m_States.get(trans.getSucc());
				addNewDownStates(cont, succCont, unpropagatedDownStates);
			}
			for (SummaryReturnTransition<LETTER, STATE> trans : returnSummarySuccessor(cont.getState())) {
				StateContainer<LETTER, STATE> succCont = m_States.get(trans.getSucc());
				addNewDownStates(cont, succCont, unpropagatedDownStates);
			}
			cont.eraseUnpropagatedDownStates();
			for (OutgoingReturnTransition<LETTER, STATE> trans : cont.returnSuccessors()) {
				StateContainer<LETTER, STATE> hierCont = m_States.get(trans.getHierPred());
				StateContainer<LETTER, STATE> succCont = m_States.get(trans.getSucc());
				STATE hierPred = trans.getHierPred();
				if (cont.hasDownProp(hierPred,DownStateProp.REACHABLE_FROM_FINAL_WITHOUT_CALL)) {
					addNewDownStates(null, succCont, hierCont.getDownStates().keySet());
					addAcceptingSummary(hierCont,succCont);
				}
			}
		}


		private void addAcceptingSummary(
				StateContainer<LETTER, STATE> callPred,
				StateContainer<LETTER, STATE> returnSucc) {
			Set<StateContainer<LETTER, STATE>> returnSuccs = m_AcceptingSummaries.get(callPred);
			if (returnSuccs == null) {
				returnSuccs = new HashSet<StateContainer<LETTER,STATE>>();
				m_AcceptingSummaries.put(callPred, returnSuccs);
			}
			returnSuccs.add(returnSucc);
		}
		
		
		

		
	    

		

	}
	
    /**
     * Offers a method to compute the strongly connected components (SCCs) of
     * the game graph.
     * Implementation of Tarjan SCC algorithm. 
     * {@link http://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm}
     * @author heizmann@informatik.uni-freiburg.de
     */
    public class StronglyConnectedComponents {
    	/**
    	 * Number of vertices that have been processed so far.
    	 */
    	int m_Index = 0;
    	/**
    	 * Vertices that have not yet been assigned to any SCC.
    	 */
    	Stack<StateContainer<LETTER, STATE>> m_NoScc = 
    			new Stack<StateContainer<LETTER, STATE>>();
    	
    	/**
    	 * Assigns to each vertex v the number of vertices that have been
    	 * processed before in this algorithm. This number is called the index
    	 * of v.
    	 */
    	Map<StateContainer<LETTER, STATE>,Integer> m_Indices = 
    			new HashMap<StateContainer<LETTER, STATE>,Integer>();

    	Map<StateContainer<LETTER, STATE>,Integer> m_LowLinks = 
    			new HashMap<StateContainer<LETTER, STATE>,Integer>();
    	
    	final Collection<SCC> m_Balls = new ArrayList<SCC>();
    	int m_NumberOfNonBallSCCs = 0;
    	
		private final Map<StateContainer<LETTER, STATE>, Set<StateContainer<LETTER, STATE>>> m_AcceptingSummaries;
		
		private final Set<StateContainer<LETTER, STATE>> m_AllStatesOfSccsWithoutCallAndReturn = 
				new HashSet<StateContainer<LETTER, STATE>>();
		
		private final List<NestedLassoRun<LETTER, STATE>> m_NestedLassoRuns = 
				new ArrayList<NestedLassoRun<LETTER, STATE>>();
		private NestedLassoRun<LETTER, STATE> m_NestedLassoRun;
		private int m_AcceptingBalls = 0;

    	
    	Collection<SCC> getBalls() {
    		return m_Balls;
    	}
    	
    	Set<StateContainer<LETTER, STATE>> getStatesOfAllSCCs() {
    		return m_AllStatesOfSccsWithoutCallAndReturn;
    	}
    	
    	public boolean buchiIsEmpty() {
    		return m_AcceptingBalls == 0;
    	}

    	
        public StronglyConnectedComponents(AcceptingSummeariesComputation asc) {
        	m_AcceptingSummaries = asc.getAcceptingSummaries();
        	for (STATE state : m_initialStates) {
        		StateContainer<LETTER, STATE> cont = m_States.get(state);
                if (!m_Indices.containsKey(cont)) {
                    strongconnect(cont);
                }
            }

            assert(automatonPartitionedBySCCs());
            for (SCC scc : m_Balls) {
            	if (scc.getAcceptingStates().size() > 0 || 
            			scc.getAcceptingSumPred().size() > 0) {
            		m_AllStatesOfSccsWithoutCallAndReturn.addAll(scc.getAllStates());
            		m_AcceptingBalls++;
            	} 
            }

            s_Logger.debug("Automaton consists of " + m_Balls.size() + 
            		" InCaSumBalls and " + m_NumberOfNonBallSCCs + 
            		" non ball SCCs " + m_AcceptingBalls + 
            		" balls are accepting. Number of states in SCCs " 
            		+ m_AllStatesOfSccsWithoutCallAndReturn.size());
        }
        
        public void computeNestedLassoRuns(boolean computeOnlyOne) {
            for (SCC scc : m_Balls) {
            	for (StateContainer<LETTER, STATE> fin  : scc.getAcceptingStates()) {
            		NestedLassoRun<LETTER, STATE> nlr = (new ShortestLassoExtractor(fin)).getNestedLassoRun();
            		if (computeOnlyOne) {
            			m_NestedLassoRun = nlr;
            		} else {
            			m_NestedLassoRuns.add(nlr);
            			if (m_NestedLassoRun == null) {
            				m_NestedLassoRun = nlr;
            			}
            		}
            	}
            	for (StateContainer<LETTER, STATE> sumPred : scc.getAcceptingSumPred()) {
            		NestedLassoRun<LETTER, STATE> nlr = (new ShortestLassoExtractor(sumPred)).getNestedLassoRun();
            		if (computeOnlyOne) {
            			m_NestedLassoRun = nlr;
            		} else {
            			m_NestedLassoRuns.add(nlr);
            			if (m_NestedLassoRun == null) {
            				m_NestedLassoRun = nlr;
            			}
            		}
            	}
            }        	
        	
        	
        }
        
        public List<NestedLassoRun<LETTER, STATE>> getAllNestedLassoRuns() {
        	return m_NestedLassoRuns;
        }
        public NestedLassoRun<LETTER, STATE> getNestedLassoRun() {
        	return m_NestedLassoRun;
        }


        private void strongconnect(StateContainer<LETTER, STATE> v) {
            assert (!m_Indices.containsKey(v));
            assert (!m_LowLinks.containsKey(v));
            m_Indices.put(v, m_Index);
            m_LowLinks.put(v, m_Index);
            m_Index++;
            this.m_NoScc.push(v);

			for (OutgoingInternalTransition<LETTER, STATE> trans : v.internalSuccessors()) {
				StateContainer<LETTER, STATE> succCont = m_States.get(trans.getSucc());
				processSuccessor(v, succCont);
			}
			for (SummaryReturnTransition<LETTER, STATE> trans : returnSummarySuccessor(v.getState())) {
				StateContainer<LETTER, STATE> succCont = m_States.get(trans.getSucc());
				processSuccessor(v, succCont);
			}
			for (OutgoingCallTransition<LETTER, STATE> trans : v.callSuccessors()) {
				StateContainer<LETTER, STATE> succCont = m_States.get(trans.getSucc());
				processSuccessor(v, succCont);
			}
            
            if (m_LowLinks.get(v).equals(m_Indices.get(v))) {
                StateContainer<LETTER, STATE> w;
                SCC scc = new SCC();
                do {
                    w = m_NoScc.pop();
                    scc.addState(w);
                } while (v != w);
                scc.setRootNode(w);
                if (isBall(scc)) {
                	m_Balls.add(scc);
                } else {
                	m_NumberOfNonBallSCCs++;
                }
            }
        }

		private void processSuccessor(StateContainer<LETTER, STATE> v,
				StateContainer<LETTER, STATE> w) {
			if (!m_Indices.containsKey(w)) {
			    strongconnect(w);
			    int minLowLink = Math.min(m_LowLinks.get(v),
			            m_LowLinks.get(w));
			    m_LowLinks.put(v, minLowLink);
			} else if (m_NoScc.contains(w)) {
			    int min = Math.min(m_LowLinks.get(v), m_Indices.get(w));
			    m_LowLinks.put(v, min);
			}
		}
        
        boolean isBall(SCC scc) {
        	if (scc.getNumberOfStates() == 1) {
        		StateContainer<LETTER, STATE> cont = scc.getRootNode();
    			for (OutgoingInternalTransition<LETTER, STATE> trans : cont.internalSuccessors()) {
    				if (trans.getSucc().equals(cont.getState())) {
    					return true;
    				}
    			}
    			for (SummaryReturnTransition<LETTER, STATE> trans : returnSummarySuccessor(cont.getState())) {
    				if (trans.getSucc().equals(cont.getState())) {
    					return true;
    				}
    			}
    			for (OutgoingCallTransition<LETTER, STATE> trans : cont.callSuccessors()) {
    				if (trans.getSucc().equals(cont.getState())) {
    					return true;
    				}
    			}
    			return false;
        	} else {
        		assert scc.getNumberOfStates() > 1;
        		return true;
        	}
        }
        
        
//        /**
//         * @return List of SCCs of the game graph in reverse topological order.
//         * (This means: If scc1 occurs in this list before scc2 then ss2 is not
//         * reachable from scc1).
//         */
//        public List<SCC> getSCCs() {
//        	assert(gameGraphPartitionedBySCCs());
//        	return m_SCCs;
//        }
        
        /**
         * @return true iff the SCCS form a partition of the automaton.
         */
        private boolean automatonPartitionedBySCCs() {
        	int statesInAllBalls = 0;
        	int max = 0;
        	for (SCC scc : m_Balls) {
        		statesInAllBalls += scc.getNumberOfStates();
        		max = Math.max(max, scc.getNumberOfStates());
        	}
        	s_Logger.debug("The biggest SCC has " + max + " vertices.");
        	boolean sameNumberOfVertices = 
        			(statesInAllBalls + m_NumberOfNonBallSCCs == m_States.size());
        	return sameNumberOfVertices;
        }
        
	    public class SCC {
	    	StateContainer<LETTER, STATE> m_RootNode;
	    	final Set<StateContainer<LETTER, STATE>> m_AcceptingStates = 
	    			new HashSet<StateContainer<LETTER, STATE>>();
	    	final Set<StateContainer<LETTER, STATE>> m_HasOutgoingAcceptingSum = 
	    			new HashSet<StateContainer<LETTER, STATE>>();
	    	final Set<StateContainer<LETTER, STATE>> m_HasAcceptingSumInSCC = 
	    			new HashSet<StateContainer<LETTER, STATE>>();
	    	final Set<StateContainer<LETTER, STATE>> m_AllStates = 
	    			new HashSet<StateContainer<LETTER, STATE>>();
	    	
	    	public void addState(StateContainer<LETTER, STATE> cont) {
	    		if (m_RootNode != null) {
	    			throw new UnsupportedOperationException(
	    					"If root node is set SCC may not be modified");
	    		}
	    		m_AllStates.add(cont);
	    		if (isFinal(cont.getState())) {
	    			m_AcceptingStates.add(cont);
	    		}
	    		if (m_AcceptingSummaries.containsKey(cont)) {
	    			m_HasOutgoingAcceptingSum.add(cont);
	    		}
	    	}
	    	

			public void setRootNode(StateContainer<LETTER, STATE> rootNode) {
	    		if (m_RootNode != null) {
	    			throw new UnsupportedOperationException(
	    					"If root node is set SCC may not be modified");
	    		}
				this.m_RootNode = rootNode;
				//TODO compute this only if there is no accepting state in
			    //SCC
				for (StateContainer<LETTER, STATE> container : m_HasOutgoingAcceptingSum) {
	    			for (StateContainer<LETTER, STATE> succ : m_AcceptingSummaries.get(container)) {
	    				if (m_AllStates.contains(succ)) {
	    					m_HasAcceptingSumInSCC.add(container);
	    				}
	    			}
				}
			}

			public int getNumberOfStates() {
				return m_AllStates.size();
			}

			public StateContainer<LETTER, STATE> getRootNode() {
				return m_RootNode;
			}
			
			public Set<StateContainer<LETTER, STATE>> getAllStates() {
				return m_AllStates;
			}

			public Set<StateContainer<LETTER, STATE>> getAcceptingStates() {
				return m_AcceptingStates;
			}

			public Set<StateContainer<LETTER, STATE>> getAcceptingSumPred() {
				return m_HasAcceptingSumInSCC;
			}
	    }
    }
    
    
    
    class LassoExtractor {
    	private final Map<StateContainer<LETTER, STATE>, Set<StateContainer<LETTER, STATE>>> m_AcceptingSummaries;
    	
    	private final NestedLassoRun<LETTER, STATE> m_nlr;
    	
    	public LassoExtractor(StateContainer<LETTER, STATE> honda, 
    			StronglyConnectedComponents.SCC scc, StateContainer<LETTER, STATE> goal, 
    			Map<StateContainer<LETTER, STATE>, Set<StateContainer<LETTER, STATE>>> acceptingSummaries) {
    			m_AcceptingSummaries = acceptingSummaries;
    			
    			LoopFinder lf = new LoopFinder(honda.getState(), scc, true, 
    					acceptingSummaries);
    			NestedRun<LETTER, STATE> loop = lf.getNestedRun();
    			NestedRun<LETTER, STATE> stem = null;
    			s_Logger.debug("Stem length: " + stem.getLength());
    			s_Logger.debug("Loop length: " + loop.getLength());
    			m_nlr = new NestedLassoRun<LETTER, STATE>(stem, loop);
    			s_Logger.debug("Stem " + stem);
    			s_Logger.debug("Loop " + loop);
    			INestedWordAutomatonOldApi<LETTER, STATE> test = NestedWordAutomatonReachableStates.this;
    			assert (new BuchiAccepts<LETTER, STATE>(test, m_nlr.getNestedLassoWord())).getResult();
    	}
    	
    	

		
		
    	class LoopFinder extends RunFinder {
    		private final StronglyConnectedComponents.SCC m_Scc;
    		
			public LoopFinder(STATE goal, StronglyConnectedComponents.SCC scc, 
					boolean visitAccepting, Map<StateContainer<LETTER, STATE>, 
					Set<StateContainer<LETTER, STATE>>> acceptingSummaries) {
				super(goal, goal, visitAccepting, acceptingSummaries);
				m_Scc = scc;
			}
			
			@Override
			protected boolean findPredecessors(STATE state, int iteration,
					boolean acceptingRequired) {
				for (IncomingReturnTransition<LETTER, STATE> inTrans : returnPredecessors(state)) {
					if (m_Scc.getAllStates().contains(inTrans.getHierPred())) {
						if (!acceptingRequired || isFinal(inTrans.getHierPred())) {
							m_SuccessorsWithGuarantee.get(iteration).put(state,
									new SummaryReturnTransition<LETTER, STATE>(inTrans.getLinPred(), inTrans.getLetter(), state));
							if (m_Goal.equals(inTrans.getHierPred())) {
								return true;
							}
						} else {
							m_SuccessorsNoGuarantee.get(iteration).put(state, 
									new SummaryReturnTransition<LETTER, STATE>(inTrans.getLinPred(), inTrans.getLetter(), state));
						}
					}
				}
				for (IncomingCallTransition<LETTER, STATE> inTrans : callPredecessors(state)) {
					if (m_Scc.getAllStates().contains(inTrans.getPred())) {
						if (!acceptingRequired || isFinal(inTrans.getPred())) {
							m_SuccessorsWithGuarantee.get(iteration).put(state,
									new OutgoingCallTransition<LETTER, STATE>(inTrans.getLetter(), state));
							if (m_Goal.equals(inTrans.getPred())) {
								return true;
							}
						} else {
							m_SuccessorsNoGuarantee.get(iteration).put(state, 
									new OutgoingCallTransition<LETTER, STATE>(inTrans.getLetter(), state));
						}
					}
				}
				for (IncomingInternalTransition<LETTER, STATE> inTrans : internalPredecessors(state)) {
					if (m_Scc.getAllStates().contains(inTrans.getPred())) {
						if (!acceptingRequired || isFinal(inTrans.getPred())) {
							m_SuccessorsWithGuarantee.get(iteration).put(
									state, new OutgoingInternalTransition<LETTER, STATE>(inTrans.getLetter(), state));
							if (m_Goal.equals(inTrans.getPred())) {
								return true;
							}
						} else {
							m_SuccessorsNoGuarantee.get(iteration).put(
									state, new OutgoingInternalTransition<LETTER, STATE>(inTrans.getLetter(), state));
						}
					}
				}
				return false;
			}

			@Override
			NestedRun<LETTER, STATE> initializeRunReconstruction() {
				NestedRun<LETTER, STATE> result = new NestedRun<LETTER, STATE>(m_Goal);
				return result;
			}
    	}
    }
    

	
	
	/**
	 * Computes an accepting nested lasso run for a given Honda state. Expects 
	 * that the Honda state is contained in an accepting SCC. Nested Runs from 
	 * the Honda to an initial state (stem) and from the Honda to the Honda are
	 * computed backwards using StacksOfFlaggedStates. The boolean flag is true
	 * iff on the path from this stack to the honda an accepting state was
	 * visited.
	 * 
	 */
	class ShortestLassoExtractor {
		
		List<Set<StackOfFlaggedStates>> m_Iterations = new ArrayList<Set<StackOfFlaggedStates>>();
		
		
		final StateContainer<LETTER, STATE> m_Goal;
		StateContainer<LETTER, STATE> m_FirstFoundInitialState;
		
		int m_GoalFoundIteration = -1;
		int m_InitFoundIteration = -1;
		
		NestedLassoRun<LETTER, STATE> m_nlr;
		NestedRun<LETTER, STATE> m_Stem;
		NestedRun<LETTER, STATE> m_Loop;
		NestedRun<LETTER, STATE> m_ConstructedNestedRun;
		
		public ShortestLassoExtractor(StateContainer<LETTER, STATE> goal) {
			m_Goal = goal;
			addInitialStack(goal);
			findPath(1);
			s_Logger.debug("Stem length: " + m_InitFoundIteration);
			s_Logger.debug("Loop length: " + m_GoalFoundIteration);
			constructStem();
			constructLoop();
			m_nlr = new NestedLassoRun<LETTER, STATE>(m_Stem, m_Loop);
			s_Logger.debug("Stem " + m_Stem);
			s_Logger.debug("Loop " + m_Loop);
			INestedWordAutomatonOldApi<LETTER, STATE> test = NestedWordAutomatonReachableStates.this;
			assert (new BuchiAccepts<LETTER, STATE>(test, m_nlr.getNestedLassoWord())).getResult();
		}

		private StackOfFlaggedStates addInitialStack(StateContainer<LETTER, STATE> goal) {
			StackOfFlaggedStates initialStack = new StackOfFlaggedStates(goal, false);
			Set<StackOfFlaggedStates> initialStacks = new HashSet<StackOfFlaggedStates>();
			initialStacks.add(initialStack);
			m_Iterations.add(initialStacks);
			return initialStack;
		}
		public NestedLassoRun<LETTER, STATE> getNestedLassoRun() {
			return m_nlr;
		}
		
		
		void findPath(final int startingIteration) {
			int i = startingIteration;
			while (m_GoalFoundIteration == -1 || m_InitFoundIteration == -1) {
				Set<StackOfFlaggedStates> currentStacks = m_Iterations.get(i-1);
				Set<StackOfFlaggedStates> preceedingStacks = new HashSet<StackOfFlaggedStates>();
				m_Iterations.add(preceedingStacks);
				for (StackOfFlaggedStates stack  : currentStacks) {
					addPreceedingStacks(i, preceedingStacks, stack);
				}
				i++;
			}
		}

		/**
		 * @param i
		 * @param preceedingStacks
		 * @param stack
		 */
		private void addPreceedingStacks(int i,
				Set<StackOfFlaggedStates> preceedingStacks,
				StackOfFlaggedStates stack) {
			StateContainer<LETTER, STATE> cont = stack.getTopmostState();
			for (IncomingInternalTransition<LETTER, STATE> inTrans : cont.internalPredecessors()) {
				StateContainer<LETTER, STATE> predCont = m_States.get(inTrans.getPred());
				boolean finalOnPathToHonda = stack.getTopmostFlag() || m_finalStates.contains(inTrans.getPred());
				if (finalOnPathToHonda && stack.height() > 1 && !stack.getSecondTopmostFlag()) {
					continue;
				}
				StackOfFlaggedStates predStack = new StackOfFlaggedStates(stack, inTrans, finalOnPathToHonda);
				preceedingStacks.add(predStack);
				checkIfGoalOrInitReached(i, predStack, predCont);
			}
			if (stack.height() == 1) {
				// call is pending
				for (IncomingCallTransition<LETTER, STATE> inTrans : cont.callPredecessors()) {
					StateContainer<LETTER, STATE> predCont = m_States.get(inTrans.getPred());
					boolean finalOnPathToHonda = stack.getTopmostFlag() || m_finalStates.contains(inTrans.getPred());
					StackOfFlaggedStates predStack = new StackOfFlaggedStates(stack, inTrans, finalOnPathToHonda);
					preceedingStacks.add(predStack);
					checkIfGoalOrInitReached(i, predStack, predCont);
				}
			} else {			
				for (IncomingCallTransition<LETTER, STATE> inTrans : cont.callPredecessors()) {
					StateContainer<LETTER, STATE> predCont = m_States.get(inTrans.getPred());
					boolean finalOnPathToHonda = stack.getTopmostFlag() || m_finalStates.contains(inTrans.getPred());
					if (!stack.getSecondTopmostState().getState().equals(inTrans.getPred())) {
						// call predecessor does not match state on stack
						continue;
					}
					if (finalOnPathToHonda != stack.getSecondTopmostFlag() && !m_finalStates.contains(inTrans.getPred())) {
						// information about finalOnPathToHonda does not match
						continue;
					}
					StackOfFlaggedStates predStack = new StackOfFlaggedStates(stack, inTrans, finalOnPathToHonda);
					preceedingStacks.add(predStack);
					checkIfGoalOrInitReached(i, predStack, predCont);
				}
			}

			// TODO: Optimization (you can ignore stacks like (q0,false)  (q0,false)  (q1,true)
			for (IncomingReturnTransition<LETTER, STATE> inTrans : cont.returnPredecessors()) {
				// note that goal or init can never be reached 
				// (backwards) with empty stack directly after return.
				int oldPreceedingStackSize = preceedingStacks.size();
				if (stack.getTopmostFlag()) {
					StackOfFlaggedStates predStack = new StackOfFlaggedStates(stack, inTrans, true, true);
					preceedingStacks.add(predStack);
				} else {
					boolean linPredIsFinal = m_finalStates.contains(inTrans.getLinPred());
					{
						StackOfFlaggedStates predStack = new StackOfFlaggedStates(stack, inTrans, true, linPredIsFinal);
						preceedingStacks.add(predStack);
					}
					if (!m_finalStates.contains(inTrans.getHierPred()) && !linPredIsFinal) {
						StackOfFlaggedStates predStack = new StackOfFlaggedStates(stack, inTrans, false, linPredIsFinal);
						preceedingStacks.add(predStack);
					}
				}
				assert oldPreceedingStackSize + 2 >= preceedingStacks.size();
			}
		}
		
		void constructStem() {
			assert m_ConstructedNestedRun == null;
			Set<StackOfFlaggedStates> initIteration = m_Iterations.get(m_InitFoundIteration);
			StackOfFlaggedStates stack = new StackOfFlaggedStates(m_FirstFoundInitialState, true);
			int sHash = stack.hashCode();
			StackOfFlaggedStates stack1 = initIteration.iterator().next();
			int sHash1  = stack1.hashCode();
			if (!initIteration.contains(stack)) {
				stack = new StackOfFlaggedStates(m_FirstFoundInitialState, false);
				sHash = stack.hashCode();
			}
			sHash = stack.hashCode();
			sHash1  = stack1.hashCode();
			sHash = stack.hashCode();
			sHash1  = stack1.hashCode();
			sHash = stack.hashCode();
			sHash1  = stack1.hashCode();
			stack.equals(stack1);
			stack.equals(stack1);
			stack.equals(stack1);

			assert initIteration.contains(stack);
			StateContainer<LETTER, STATE> cont = m_FirstFoundInitialState;
			m_ConstructedNestedRun = new NestedRun<LETTER, STATE>(cont.getState());
			for (int i = m_InitFoundIteration-1; i>=0; i--) {
				stack = getSuccessorStack(stack, m_Iterations.get(i));
			}
			m_Stem = m_ConstructedNestedRun;
			m_ConstructedNestedRun = null;
		}
		
		void constructLoop() {
			Set<StackOfFlaggedStates> hondaIteration = m_Iterations.get(m_GoalFoundIteration);
			StackOfFlaggedStates stack = new StackOfFlaggedStates(m_Goal, true);
			if (!hondaIteration.contains(stack)) {
				stack = new StackOfFlaggedStates(m_Goal, false);
			}
			assert hondaIteration.contains(stack);
			StateContainer<LETTER, STATE> cont = m_Goal;
			m_ConstructedNestedRun = new NestedRun<LETTER, STATE>(cont.getState());
			m_Loop = new NestedRun<LETTER, STATE>(cont.getState());
			for (int i = m_GoalFoundIteration-1; i>=0; i--) {
				stack = getSuccessorStack(stack, m_Iterations.get(i));
			}
			m_Loop = m_ConstructedNestedRun;
			m_ConstructedNestedRun = null;
		}

		
		StackOfFlaggedStates getSuccessorStack(StackOfFlaggedStates sofs, Set<StackOfFlaggedStates> succCandidates) {
			StateContainer<LETTER, STATE> cont = sofs.getTopmostState();
			if (sofs.getTopmostFlag()) {
				for (OutgoingInternalTransition<LETTER, STATE> outTrans : cont.internalSuccessors()) {
					StackOfFlaggedStates succStack = new StackOfFlaggedStates(sofs, outTrans, true);
					if (succCandidates.contains(succStack)) {
						NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
								cont.getState(), outTrans.getLetter(), NestedWord.INTERNAL_POSITION, outTrans.getSucc());
						m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
						return succStack;
					}
				}
				for (OutgoingCallTransition<LETTER, STATE> outTrans : cont.callSuccessors()) {
					StackOfFlaggedStates succStack = new StackOfFlaggedStates(sofs, outTrans, true, false);
					if (succCandidates.contains(succStack)) {
						NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
								cont.getState(), outTrans.getLetter(), NestedWord.PLUS_INFINITY, outTrans.getSucc());
						m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
						return succStack;
					}
					if (sofs.height() == 1) {
						//check also for pending calls
						succStack = new StackOfFlaggedStates(sofs, outTrans, true, true);
						if (succCandidates.contains(succStack)) {
							NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
									cont.getState(), outTrans.getLetter(), NestedWord.PLUS_INFINITY, outTrans.getSucc());
							m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
							return succStack;
						}

					}
				}
				if (sofs.height() > 1) {
					for (OutgoingReturnTransition<LETTER, STATE> outTrans : cont.returnSuccessors()) {
						if (sofs.getSecondTopmostState().getState().equals(outTrans.getHierPred())) {
							StackOfFlaggedStates succStack = new StackOfFlaggedStates(sofs, outTrans, true);
							if (succCandidates.contains(succStack)) {
								NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
										cont.getState(), outTrans.getLetter(), NestedWord.MINUS_INFINITY, outTrans.getSucc());
								m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
								return succStack;
							}
						}
					}
				}
			}
			for (OutgoingInternalTransition<LETTER, STATE> outTrans : cont.internalSuccessors()) {
				StackOfFlaggedStates succStack = new StackOfFlaggedStates(sofs, outTrans, false);
				if (succCandidates.contains(succStack)) {
					NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
							cont.getState(), outTrans.getLetter(), NestedWord.INTERNAL_POSITION, outTrans.getSucc());
					m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
					return succStack;
				}
			}
			for (OutgoingCallTransition<LETTER, STATE> outTrans : cont.callSuccessors()) {
				StackOfFlaggedStates succStack = new StackOfFlaggedStates(sofs, outTrans, false, false);
				if (succCandidates.contains(succStack)) {
					NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
							cont.getState(), outTrans.getLetter(), NestedWord.PLUS_INFINITY, outTrans.getSucc());
					m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
					return succStack;
				}
				if (sofs.height() == 1) {
					//check also for pending calls
					succStack = new StackOfFlaggedStates(sofs, outTrans, false, true);
					if (succCandidates.contains(succStack)) {
						NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
								cont.getState(), outTrans.getLetter(), NestedWord.PLUS_INFINITY, outTrans.getSucc());
						m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
						return succStack;
					}

				}
			}
			if (sofs.height() > 1) {
				for (OutgoingReturnTransition<LETTER, STATE> outTrans : cont.returnSuccessors()) {
					if (sofs.getSecondTopmostState().getState().equals(outTrans.getHierPred())) {
						StackOfFlaggedStates succStack = new StackOfFlaggedStates(sofs, outTrans, false);
						if (succCandidates.contains(succStack)) {
							NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
									cont.getState(), outTrans.getLetter(), NestedWord.MINUS_INFINITY, outTrans.getSucc());
							m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
							return succStack;
						}
					}
				}
			}
			throw new AssertionError("no corresponding state found");
		}


		/**
		 * @param i
		 * @param stack
		 * @param inTrans
		 * @param predCont
		 */
		private void checkIfGoalOrInitReached(int i,
				StackOfFlaggedStates stack,
				StateContainer<LETTER, STATE> predCont) {
			if (predCont == m_Goal && stack.hasOnlyTopmostElement() && 
					stack.getTopmostFlag() == true) {
				m_GoalFoundIteration = i;
			}
			if (m_FirstFoundInitialState == null && 
					m_initialStates.contains(predCont.getState()) && 
					stack.hasOnlyTopmostElement()) {
				m_InitFoundIteration = i;
				m_FirstFoundInitialState = predCont;
			}
		}
		
		
		class StackOfFlaggedStates {
			private final StateContainer<LETTER, STATE> m_TopmostState;
			private final boolean m_TopmostFlag;
			private final StateContainer<LETTER, STATE>[] m_StateStack;
			private final boolean[] m_FlagStack;
			
			public int height() {
				return m_StateStack.length + 1;
			}
			


			/**
			 * Returns true if there is only one element on the stack, i.e., if 
			 * the topmost element is the only element on the stack.
			 */
			public boolean hasOnlyTopmostElement() {
				return m_StateStack.length == 0;
			}
			
			public StateContainer<LETTER, STATE> getSecondTopmostState() {
				return m_StateStack[m_StateStack.length-1];
			}

			public StateContainer<LETTER, STATE> getTopmostState() {
				return m_TopmostState;
			}
			
			public boolean getSecondTopmostFlag() {
				return m_FlagStack[m_FlagStack.length-1];
			}

			public boolean getTopmostFlag() {
				return m_TopmostFlag;
			}
			
			@SuppressWarnings("unchecked")
			public StackOfFlaggedStates(StateContainer<LETTER, STATE> cont, boolean flag) {
				m_StateStack = new StateContainer[0];
				m_FlagStack = new boolean[0];
				m_TopmostState = cont;
				m_TopmostFlag = flag;
			}

			public StackOfFlaggedStates(StackOfFlaggedStates sofs, 
					IncomingInternalTransition<LETTER, STATE> inTrans, boolean flag) {
				m_StateStack = sofs.m_StateStack;
				m_FlagStack = sofs.m_FlagStack;
				m_TopmostState = m_States.get(inTrans.getPred());
				m_TopmostFlag = flag;
			}
			
			public StackOfFlaggedStates(StackOfFlaggedStates sofs, 
					IncomingCallTransition<LETTER, STATE> inTrans, boolean flag) {
				if (sofs.m_StateStack.length == 0) {
					m_StateStack = sofs.m_StateStack;
					m_FlagStack = sofs.m_FlagStack;
					m_TopmostState = m_States.get(inTrans.getPred());
					m_TopmostFlag = flag;
					
				} else {
					m_StateStack = Arrays.copyOf(sofs.m_StateStack, sofs.m_StateStack.length-1); 
					m_FlagStack = Arrays.copyOf(sofs.m_FlagStack, sofs.m_FlagStack.length-1);
					m_TopmostState = m_States.get(inTrans.getPred());
					m_TopmostFlag = flag;
				}
			}
			
			public StackOfFlaggedStates(StackOfFlaggedStates sofs, 
					IncomingReturnTransition<LETTER, STATE> inTrans, boolean hierFlag, boolean linFlag) {
					m_StateStack = Arrays.copyOf(sofs.m_StateStack, sofs.m_StateStack.length+1); 
					m_FlagStack = Arrays.copyOf(sofs.m_FlagStack, sofs.m_FlagStack.length+1);
					m_StateStack[m_StateStack.length-1] = m_States.get(inTrans.getHierPred());
					m_FlagStack[m_StateStack.length-1] = hierFlag;
					m_TopmostState = m_States.get(inTrans.getLinPred());
					m_TopmostFlag = linFlag;
			}

			
			public StackOfFlaggedStates(StackOfFlaggedStates sofs, 
					OutgoingInternalTransition<LETTER, STATE> outTrans, boolean flag) {
				m_StateStack = sofs.m_StateStack;
				m_FlagStack = sofs.m_FlagStack;
				m_TopmostState = m_States.get(outTrans.getSucc());
				m_TopmostFlag = flag;
			}
			
			public StackOfFlaggedStates(StackOfFlaggedStates sofs, 
					OutgoingCallTransition<LETTER, STATE> outTrans, boolean flag, boolean isPending) {
				if (isPending) {
					m_StateStack = sofs.m_StateStack;
					m_FlagStack = sofs.m_FlagStack;
					m_TopmostState = m_States.get(outTrans.getSucc());
					m_TopmostFlag = flag;
				} else {
					m_StateStack = Arrays.copyOf(sofs.m_StateStack, sofs.m_StateStack.length+1); 
					m_FlagStack = Arrays.copyOf(sofs.m_FlagStack, sofs.m_FlagStack.length+1);
					m_StateStack[m_StateStack.length-1] = sofs.m_TopmostState;
					m_FlagStack[m_StateStack.length-1] = sofs.m_TopmostFlag;
					m_TopmostState = m_States.get(outTrans.getSucc());
					m_TopmostFlag = flag;
				}
			}
			
			public StackOfFlaggedStates(StackOfFlaggedStates sofs, 
					OutgoingReturnTransition<LETTER, STATE> outTrans, boolean flag) {
					m_StateStack = Arrays.copyOf(sofs.m_StateStack, sofs.m_StateStack.length-1); 
					m_FlagStack = Arrays.copyOf(sofs.m_FlagStack, sofs.m_FlagStack.length-1);
					m_TopmostState = m_States.get(outTrans.getSucc());
					m_TopmostFlag = flag;
			}

			@Override
			public int hashCode() {
				int result = HashUtils.hashJenkins((new Boolean(m_TopmostFlag)).hashCode(), m_TopmostState);
//				result = HashUtils.hashJenkins(result, m_FlagStack);
				result = HashUtils.hashJenkins(result, m_StateStack);
				return result;
			}

			@Override
			public boolean equals(Object obj) {
				if (this == obj)
					return true;
				if (obj == null)
					return false;
				if (getClass() != obj.getClass())
					return false;
				StackOfFlaggedStates other = (StackOfFlaggedStates) obj;
				if (!getOuterType().equals(other.getOuterType()))
					return false;
				if (!Arrays.equals(m_FlagStack, other.m_FlagStack))
					return false;
				if (!Arrays.equals(m_StateStack, other.m_StateStack))
					return false;
				if (m_TopmostFlag != other.m_TopmostFlag)
					return false;
				if (m_TopmostState == null) {
					if (other.m_TopmostState != null)
						return false;
				} else if (!m_TopmostState.equals(other.m_TopmostState))
					return false;
				return true;
			}

			private ShortestLassoExtractor getOuterType() {
				return ShortestLassoExtractor.this;
			}

			@Override
			public String toString() {
				StringBuilder sb = new StringBuilder();
				for (int i=0; i<m_StateStack.length; i++) {
					sb.append("(" + m_StateStack[i].getState() + "," + m_FlagStack[i] + ")  ");
				}
				sb.append("(" + m_TopmostState.getState() + "," + m_TopmostFlag + ")");
				return sb.toString();
			}
			
			
		}
	}
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	

	

	
	
	
	
	
	
	

	

	

	
	


	
	

	
	/**
	 * Construct a run that starts in an initial state and ends in end.
	 */
	private NestedRun<LETTER, STATE> constructRun(final StateContainer<LETTER,STATE> end) {
		StateContainer<LETTER,STATE> current = end;
		Object transitionToLowest = null;
		int lowestPredecessorSerialNumber = Integer.MAX_VALUE;
		NestedRun<LETTER,STATE> result = new NestedRun<LETTER,STATE>(end.getState());
		
		while (!isInitial(current.getState())) {
			for (IncomingReturnTransition<LETTER, STATE> inTrans : returnPredecessors(current.getState())) {
				StateContainer<LETTER,STATE> predSc = m_States.get(inTrans.getHierPred());
				int predSerialNumber = predSc.getSerialNumber();
				if (predSerialNumber < lowestPredecessorSerialNumber) {
					lowestPredecessorSerialNumber = predSerialNumber;
					transitionToLowest = inTrans;
				}
			}
			for (IncomingCallTransition<LETTER, STATE> inTrans : callPredecessors(current.getState())) {
				StateContainer<LETTER,STATE> predSc = m_States.get(inTrans.getPred());
				int predSerialNumber = predSc.getSerialNumber();
				if (predSerialNumber < lowestPredecessorSerialNumber) {
					lowestPredecessorSerialNumber = predSerialNumber;
					transitionToLowest = inTrans;
				}
			}
			for (IncomingInternalTransition<LETTER, STATE> inTrans : internalPredecessors(current.getState())) {
				StateContainer<LETTER,STATE> predSc = m_States.get(inTrans.getPred());
				int predSerialNumber = predSc.getSerialNumber();
				if (predSerialNumber < lowestPredecessorSerialNumber) {
					lowestPredecessorSerialNumber = predSerialNumber;
					transitionToLowest = inTrans;
				}
			}
			NestedRun<LETTER,STATE> newPrefix;
			if (transitionToLowest instanceof IncomingInternalTransition) {
				IncomingInternalTransition<LETTER, STATE> inTrans = (IncomingInternalTransition) transitionToLowest;
				newPrefix = new NestedRun(inTrans.getPred(), inTrans.getLetter(), NestedWord.INTERNAL_POSITION ,current.getState());
			} else if (transitionToLowest instanceof IncomingCallTransition) {
				IncomingCallTransition<LETTER, STATE> inTrans = (IncomingCallTransition) transitionToLowest;
				newPrefix = new NestedRun(inTrans.getPred(), inTrans.getLetter(), NestedWord.PLUS_INFINITY ,current.getState());
			} else if (transitionToLowest instanceof IncomingReturnTransition) {
				IncomingReturnTransition<LETTER, STATE> inTrans = (IncomingReturnTransition) transitionToLowest;
				SummaryFinder summaryFinder = new SummaryFinder(
						current.getState(), inTrans.getHierPred(), 
						false, null);
				NestedRun<LETTER, STATE> summary = summaryFinder.getNestedRun();
				NestedRun<LETTER, STATE> returnSuffix = 
						new NestedRun<LETTER, STATE>(inTrans.getLinPred(), 
								inTrans.getLetter(), 
								NestedWord.MINUS_INFINITY, current.getState());
				summary = summary.concatenate(returnSuffix);
				newPrefix = summary;
			} else {
				throw new AssertionError();
			}
			result = newPrefix.concatenate(result);
			current = m_States.get(result.getStateAtPosition(0));
			transitionToLowest = null;
			lowestPredecessorSerialNumber = Integer.MAX_VALUE;
		}
		return result;
	}
	
	

	
	
	

	
	


	
	

	
	
	
	
	
	
	
	
	
	
	
	
	


	abstract class RunFinder {
		protected final STATE m_Start;
		protected final STATE m_Goal;
		/**
		 * If true we search only for runs that visit an accepting state.
		 */
		protected final boolean m_VisitAccepting;
		/**
		 * Successor mapping. If you build a path starting with this mapping
		 * it is guaranteed that the requirement (e.g., final state visited)
		 * is fulfilled. If you are rebuilding a run and requirement is 
		 * already met, my may need m_SuccessorsNoGuarantee for the 
		 * remainder of the run.
		 * If there is no requirement all successor informations are in 
		 * these Maps.
		 */
		protected final List<Map<STATE, Object>> m_SuccessorsWithGuarantee;
		
		/**
		 * Successor mapping. I you use this to build a run, it is not
		 * guaranteed that the requirement (e.g., final state visited) is
		 * fulfilled.
		 */
		protected final List<Map<STATE, Object>> m_SuccessorsNoGuarantee;
		
		/**
		 * Contains a pair of states (pre,post) if there is an run from
		 * pre to post such that
		 * - this run visits an accepting state
		 * - this run starts with a call
		 * - this run ends with a return
		 * 
		 * May be null if visiting an accepting state is not required.
		 */
		private final Map<StateContainer<LETTER, STATE>, 
					Set<StateContainer<LETTER, STATE>>> m_AcceptingSummaries;
		
		
		public RunFinder(STATE start, STATE goal, boolean visitAccepting, 
				Map<StateContainer<LETTER, STATE>, 
				Set<StateContainer<LETTER, STATE>>> acceptingSummaries) {
			m_Start = start;
			m_Goal = goal;
			m_VisitAccepting = visitAccepting;
			m_AcceptingSummaries = acceptingSummaries;
			m_SuccessorsWithGuarantee = new ArrayList<Map<STATE,Object>>();
			m_SuccessorsNoGuarantee = new ArrayList<Map<STATE,Object>>();
		}
		
		public NestedRun<LETTER, STATE> getNestedRun() {
			find(m_Start);
			return constructRun();
		}
		
		protected boolean isAcceptingSummary(STATE pre, STATE post) {
			StateContainer<LETTER, STATE> preSc = m_States.get(pre);
			Set<StateContainer<LETTER, STATE>> postCandidates = m_AcceptingSummaries.get(preSc);
			if (postCandidates == null) {
				return false;
			} else {
				StateContainer<LETTER, STATE> postSc = m_States.get(pre);
				return postCandidates.contains(postSc);
			}
		}
		
		private void find(STATE start) {
			int iteration = 0;
			m_SuccessorsWithGuarantee.add(new HashMap<STATE,Object>());
			m_SuccessorsNoGuarantee.add(new HashMap<STATE,Object>());
			boolean found = findPredecessors(start, iteration, m_VisitAccepting);
			while(!found) {
				for (STATE state : m_SuccessorsWithGuarantee.get(iteration).keySet()) {
					findPredecessors(state, iteration, false);
				}
				for (STATE state : m_SuccessorsNoGuarantee.get(iteration).keySet()) {
					findPredecessors(state, iteration, true);
				}
			}
		}
		
		protected abstract boolean findPredecessors(STATE state, int iteration, boolean acceptingRequired);
	
	
		abstract NestedRun<LETTER, STATE> initializeRunReconstruction();
		
		/**
		 * Construct the run that has been found.
		 * @return
		 */
		private NestedRun<LETTER, STATE> constructRun() {
			boolean visitAcceptingStillRequired = m_VisitAccepting;
			NestedRun<LETTER, STATE> result = initializeRunReconstruction(); 
					
			for (int i = m_SuccessorsWithGuarantee.size() - 1; i>=0; i--) {
				STATE currentState = result.getStateAtPosition(result.getLength());
				if (isFinal(currentState)) {
					visitAcceptingStillRequired = false;
				}
				Object succs = m_SuccessorsWithGuarantee.get(i).get(currentState);
				if(succs == null) {
					succs = m_SuccessorsNoGuarantee.get(i).get(currentState);
				}
				assert succs != null;
				NestedRun<LETTER, STATE> newSuffix;
				if (succs instanceof OutgoingInternalTransition) {
					OutgoingInternalTransition<LETTER, STATE> outTrans = 
							(OutgoingInternalTransition<LETTER, STATE>) succs;
					newSuffix = new NestedRun<LETTER, STATE>(currentState, 
							outTrans.getLetter(), 
							NestedWord.INTERNAL_POSITION, outTrans.getSucc());
					result = result.concatenate(newSuffix);
				} else if (succs instanceof OutgoingCallTransition) {
					OutgoingCallTransition<LETTER, STATE> outTrans = 
							(OutgoingCallTransition<LETTER, STATE>) succs;
					newSuffix = new NestedRun<LETTER, STATE>(currentState, 
							outTrans.getLetter(), 
							NestedWord.PLUS_INFINITY, outTrans.getSucc());
				} else if (succs instanceof SummaryReturnTransition) {
					SummaryReturnTransition<LETTER, STATE> outTrans = 
							(SummaryReturnTransition<LETTER, STATE>) succs;
					boolean findAcceptingSummary;
					if (visitAcceptingStillRequired) {
						if (isAcceptingSummary(currentState, outTrans.getSucc())) {
							findAcceptingSummary = true;
						} else {
							findAcceptingSummary = false;
						}
					} else {
						findAcceptingSummary = false;
					}
					SummaryFinder summaryFinder = new SummaryFinder(
							outTrans.getSucc(), currentState, 
							findAcceptingSummary, m_AcceptingSummaries);
					newSuffix = summaryFinder.getNestedRun();
					NestedRun<LETTER, STATE> retSuffix = 
							new NestedRun<LETTER, STATE>(outTrans.getLinPred(), 
							outTrans.getLetter(), 
							NestedWord.MINUS_INFINITY, outTrans.getSucc());
					newSuffix = newSuffix.concatenate(retSuffix);
					if (findAcceptingSummary) {
						visitAcceptingStillRequired = false;
					}
				} else {
					throw new AssertionError("unknown transition");
				}
				result = result.concatenate(newSuffix);
			}
			return result;
		}
	}












	class SummaryFinder extends RunFinder {
	
		OutgoingCallTransition<LETTER, STATE> m_Call;
		
		public SummaryFinder(STATE returnPredecessor, STATE callPredecessor, 
				boolean visitAccepting,	Map<StateContainer<LETTER, STATE>, 
						Set<StateContainer<LETTER, STATE>>> acceptingSummaries) {
			super(returnPredecessor, callPredecessor, visitAccepting, acceptingSummaries);
		}
		
		protected boolean findPredecessors(STATE state, int iteration, boolean acceptingRequired) {
			if (!acceptingRequired) {
				for (IncomingCallTransition<LETTER, STATE> inTrans : callPredecessors(state)) {
					if (m_Goal.equals(inTrans.getPred())) {
						m_Call = new OutgoingCallTransition<LETTER, STATE>(inTrans.getLetter(), state);
						return true;
					}
				}
			}
			for (IncomingInternalTransition<LETTER, STATE> inTrans : internalPredecessors(state)) {
				StateContainer<LETTER, STATE> predSc = m_States.get(inTrans.getPred());
				if (predSc.getDownStates().containsKey(m_Goal)) {
					if (acceptingRequired) {
						if (isFinal(predSc.getState())) {
							m_SuccessorsWithGuarantee.get(iteration).put(
									state, new OutgoingInternalTransition<LETTER, STATE>(inTrans.getLetter(), state));
						} else if (predSc.hasDownProp(m_Goal, DownStateProp.REACHABLE_FROM_FINAL_WITHOUT_CALL)) {
							m_SuccessorsNoGuarantee.get(iteration).put(
									state, new OutgoingInternalTransition<LETTER, STATE>(inTrans.getLetter(), state));
						}
					} else {
						m_SuccessorsWithGuarantee.get(iteration).put(
								state, new OutgoingInternalTransition<LETTER, STATE>(inTrans.getLetter(), state));
					}
				}
			}
			for (IncomingReturnTransition<LETTER, STATE> inTrans : returnPredecessors(state)) {
				StateContainer<LETTER, STATE> predSc = m_States.get(inTrans.getHierPred());
				if (predSc.getDownStates().containsKey(m_Goal)) {
					if (acceptingRequired) {
						if (isFinal(predSc.getState())) {
							m_SuccessorsWithGuarantee.get(iteration).put(
									state, new SummaryReturnTransition<LETTER, STATE>(inTrans.getLinPred(), inTrans.getLetter(), state));
						} else if (isAcceptingSummary(inTrans.getHierPred(), state)) {
							m_SuccessorsWithGuarantee.get(iteration).put(
									state, new SummaryReturnTransition<LETTER, STATE>(inTrans.getLinPred(), inTrans.getLetter(), state));
						} else if (predSc.hasDownProp(m_Goal, DownStateProp.REACHABLE_FROM_FINAL_WITHOUT_CALL)) {
							m_SuccessorsNoGuarantee.get(iteration).put(
									state, new SummaryReturnTransition<LETTER, STATE>(inTrans.getLinPred(), inTrans.getLetter(), state));
						}
					} else {
						m_SuccessorsWithGuarantee.get(iteration).put(
								state, new SummaryReturnTransition<LETTER, STATE>(inTrans.getLinPred(), inTrans.getLetter(), state));
					}
				}
			}
			return false;
		}
		
		@Override
		NestedRun<LETTER, STATE> initializeRunReconstruction() {
			return new NestedRun<LETTER, STATE>(m_Goal, m_Call.getLetter(), NestedWord.PLUS_INFINITY,m_Call.getSucc());
		}
	}

































































	////////////////////////////////////////////////////////////////////////////
	// Methods to check correctness
	



	public boolean containsInternalTransition(STATE state, LETTER letter, STATE succ) {
		return m_States.get(state).containsInternalTransition(letter, succ);
	}
	
	public boolean containsCallTransition(STATE state, LETTER letter, STATE succ) {
		return m_States.get(state).containsCallTransition(letter, succ);
	}
	
	public boolean containsReturnTransition(STATE state, STATE hier, LETTER letter, STATE succ) {
		return m_States.get(state).containsReturnTransition(hier, letter, succ);
	}
	
	protected boolean containsSummaryReturnTransition(STATE lin, STATE hier, LETTER letter, STATE succ) {
		for (SummaryReturnTransition<LETTER, STATE> trans : returnSummarySuccessor(letter, hier)) {
			if (succ.equals(trans.getSucc()) && lin.equals(trans.getLinPred())) {
				return true;
			}
		}
		return false;
	}
	
	private boolean checkTransitionsReturnedConsistent() {
		boolean result = true;
		for (STATE state : getStates()) {
			for (IncomingInternalTransition<LETTER, STATE> inTrans : internalPredecessors(state)) {
				result &= containsInternalTransition(inTrans.getPred(), inTrans.getLetter(), state);
				assert result;
				StateContainer<LETTER, STATE> cont  = m_States.get(state); 
				result &= cont.lettersInternalIncoming().contains(inTrans.getLetter());
				assert result;
				result &= cont.predInternal(inTrans.getLetter()).contains(inTrans.getPred());
				assert result;
			}
			for (OutgoingInternalTransition<LETTER, STATE> outTrans : internalSuccessors(state)) {
				result &= containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert result;
				StateContainer<LETTER, STATE> cont  = m_States.get(state);
				result &= cont.lettersInternal().contains(outTrans.getLetter());
				assert result;
				result &= cont.succInternal(outTrans.getLetter()).contains(outTrans.getSucc());
				assert result;
			}
			for (IncomingCallTransition<LETTER, STATE> inTrans : callPredecessors(state)) {
				result &= containsCallTransition(inTrans.getPred(), inTrans.getLetter(), state);
				assert result;
				StateContainer<LETTER, STATE> cont  = m_States.get(state);
				result &= cont.lettersCallIncoming().contains(inTrans.getLetter());
				assert result;
				result &= cont.predCall(inTrans.getLetter()).contains(inTrans.getPred());
				assert result;
			}
			for (OutgoingCallTransition<LETTER, STATE> outTrans : callSuccessors(state)) {
				result &= containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert result;
				StateContainer<LETTER, STATE> cont  = m_States.get(state);
				result &= cont.lettersCall().contains(outTrans.getLetter());
				assert result;
				result &= cont.succCall(outTrans.getLetter()).contains(outTrans.getSucc());
				assert result;
			}
			for (IncomingReturnTransition<LETTER, STATE> inTrans : returnPredecessors(state)) {
				result &= containsReturnTransition(inTrans.getLinPred(), inTrans.getHierPred(), inTrans.getLetter(), state);
				assert result;
				result &= containsSummaryReturnTransition(inTrans.getLinPred(), inTrans.getHierPred(), inTrans.getLetter(), state);
				assert result;
				StateContainer<LETTER, STATE> cont  = m_States.get(state);
				result &= cont.lettersReturnIncoming().contains(inTrans.getLetter());
				assert result;
				result &= cont.predReturnHier(inTrans.getLetter()).contains(inTrans.getHierPred());
				assert result;
				result &= cont.predReturnLin(inTrans.getLetter(),inTrans.getHierPred()).contains(inTrans.getLinPred());
				assert result;
			}
			for (OutgoingReturnTransition<LETTER, STATE> outTrans : returnSuccessors(state)) {
				result &= containsReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());
				assert result;
				result &= containsSummaryReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());
				assert result;
				StateContainer<LETTER, STATE> cont  = m_States.get(state);
				result &= cont.lettersReturn().contains(outTrans.getLetter());
				assert result;
				result &= cont.hierPred(outTrans.getLetter()).contains(outTrans.getHierPred());
				assert result;
				result &= cont.succReturn(outTrans.getHierPred(),outTrans.getLetter()).contains(outTrans.getSucc());
				assert result;
			}
//			for (LETTER letter : lettersReturnSummary(state)) {
//				for (SummaryReturnTransition<LETTER, STATE> sumTrans : returnSummarySuccessor(letter, state)) {
//				result &= containsReturnTransition(state, sumTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());
//				assert result;
//				StateContainer<LETTER, STATE> cont  = m_States.get(state);
//				result &= cont.lettersReturn().contains(outTrans.getLetter());
//				assert result;
//				result &= cont.hierPred(outTrans.getLetter()).contains(outTrans.getHierPred());
//				assert result;
//				result &= cont.succReturn(outTrans.getHierPred(),outTrans.getLetter()).contains(outTrans.getSucc());
//				assert result;
//				}
//			}
			
			
			for (LETTER letter : lettersInternal(state)) {
				for (STATE succ : succInternal(state, letter)) {
					result &= containsInternalTransition(state, letter, succ);
					assert result;
				}
			}
			for (LETTER letter : lettersCall(state)) {
				for (STATE succ : succCall(state, letter)) {
					result &= containsCallTransition(state, letter, succ);
					assert result;
				}
			}
			for (LETTER letter : lettersReturn(state)) {
				for (STATE hier : hierPred(state, letter)) {
					for (STATE succ : succReturn(state, hier, letter)) {
						result &= containsReturnTransition(state, hier, letter, succ);
						assert result;
					}
				}
			}
			for (LETTER letter : lettersInternalIncoming(state)) {
				for (STATE pred : predInternal(state, letter)) {
					result &= containsInternalTransition(pred, letter, state);
					assert result;
				}
			}
			for (LETTER letter : lettersCallIncoming(state)) {
				for (STATE pred : predCall(state, letter)) {
					result &= containsCallTransition(pred, letter, state);
					assert result;
				}
			}
			for (LETTER letter : lettersReturnIncoming(state)) {
				for (STATE hier : predReturnHier(state, letter)) {
					for (STATE lin : predReturnLin(state, letter, hier)) {
						result &= containsReturnTransition(lin, hier, letter, state);
						assert result;
					}
				}
			}
			
		}

		return result;
	}
	
//	private boolean cecSumConsistent() {
//		int sum = 0;
//		for (CommonEntriesComponent<LETTER,STATE> cec : m_AllCECs) {
//			sum += cec.m_Size;
//		}
//		int allStates = m_States.keySet().size();
//		return sum == allStates;
//	}
//	
//	private boolean allStatesAreInTheirCec() {
//		boolean result = true;
//		for (STATE state : m_States.keySet()) {
//			StateContainer<LETTER,STATE> sc = m_States.get(state);
//			CommonEntriesComponent<LETTER,STATE> cec = sc.getCommonEntriesComponent();
//			if (!cec.m_BorderOut.keySet().contains(sc)) {
//				Set<StateContainer<LETTER,STATE>> empty = new HashSet<StateContainer<LETTER,STATE>>();
//				result &= internalOutSummaryOutInCecOrForeigners(sc, empty, cec);
//			}
//		}
//		return result;
//	}
//	
//	private boolean occuringStatesAreConsistent(CommonEntriesComponent<LETTER,STATE> cec) {
//		boolean result = true;
//		Set<STATE> downStates = cec.m_DownStates;
//		Set<Entry<LETTER,STATE>> entries = cec.m_Entries;
//		if (cec.m_Size > 0) {
//			result &= downStatesAreCallPredsOfEntries(downStates, entries);
//		}
//		assert (result);
//		result &= eachStateHasThisCec(cec.getReturnOutCandidates(), cec);
//		assert (result);
//		for (StateContainer<LETTER, STATE> resident : cec.m_BorderOut.keySet()) {
//			Set<StateContainer<LETTER,STATE>> foreignerSCs = cec.m_BorderOut.get(resident);
//			result &= internalOutSummaryOutInCecOrForeigners(resident, foreignerSCs, cec);
//			assert (result);
//		}
//		return result;
//	}
//	
//	
//	private boolean downStatesConsistentwithEntriesDownStates(CommonEntriesComponent<LETTER,STATE> cec) {
//		boolean result = true;
//		Set<STATE> downStates = cec.m_DownStates;
//		Set<Entry<LETTER,STATE>> entries = cec.m_Entries;
//		Set<STATE> downStatesofEntries = new HashSet<STATE>();
//		for (Entry<LETTER,STATE> entry : entries) {
//			downStatesofEntries.addAll(entry.getDownStates().keySet());
//		}
//		result &= isSubset(downStates, downStatesofEntries);
//		assert (result);
//		result &= isSubset(downStatesofEntries, downStates);
//		assert (result);
//		return result;
//	}
//	
//	private boolean internalOutSummaryOutInCecOrForeigners(StateContainer<LETTER, STATE> state, Set<StateContainer<LETTER,STATE>> foreigners, CommonEntriesComponent<LETTER,STATE> cec) {
//		Set<StateContainer<LETTER,STATE>> neighbors = new HashSet<StateContainer<LETTER,STATE>>();
//		
//		for (OutgoingInternalTransition<LETTER, STATE> trans : state.internalSuccessors()) {
//			STATE succ = trans.getSucc();
//			StateContainer<LETTER,STATE> succSc = m_States.get(succ);
//			if (succSc.getCommonEntriesComponent() == cec) {
//				// do nothing
//			} else {
//				neighbors.add(succSc);
//			}
//		}
//		if (m_Summaries.containsKey(state)) {
//			for (StateContainer<LETTER,STATE> succSc : m_Summaries.get(state)) {
//				if (succSc.getCommonEntriesComponent() == cec) {
//					// do nothing
//				} else {
//					neighbors.add(succSc);
//				}
//			}
//		}
//		boolean allNeighborAreForeigners = isSubset(neighbors, foreigners);
//		assert allNeighborAreForeigners;
//		boolean allForeignersAreNeighbor = isSubset(foreigners, neighbors);
//		assert allForeignersAreNeighbor;
//		return allNeighborAreForeigners && allForeignersAreNeighbor;
//	}
//	
//	private boolean eachStateHasThisCec(Set<STATE> states, CommonEntriesComponent<LETTER,STATE> cec) {
//		boolean result = true;
//		for (STATE state : states) {
//			StateContainer<LETTER, STATE> sc = m_States.get(state);
//			if (sc.getCommonEntriesComponent() != cec) {
//				result = false;
//				assert result;
//			}
//		}
//		return result;
//	}
//	
//	private boolean downStatesAreCallPredsOfEntries(Set<STATE> downStates, Set<Entry<LETTER,STATE>> entries) {
//		Set<STATE> callPreds = new HashSet<STATE>();
//		for (Entry<LETTER,STATE> entry : entries) {
//			STATE entryState = entry.getState();
//			if (isInitial(entryState)) {
//				callPreds.add(getEmptyStackState());
//			}
//			for (IncomingCallTransition<LETTER, STATE> trans : callPredecessors(entryState)) {
//				callPreds.add(trans.getPred());
//			}
//		}
//		boolean callPredsIndownStates = isSubset(callPreds, downStates);
//		assert (callPredsIndownStates);
//		boolean downStatesInCallPreds = isSubset(downStates, callPreds);
//		assert (downStatesInCallPreds);
//		return callPredsIndownStates && downStatesInCallPreds;
//	}
//	
//	private boolean isBorderOutConsistent(StateContainer<LETTER,STATE> cont) {
//		CommonEntriesComponent<LETTER, STATE> cec = cont.getCommonEntriesComponent();
//		ArrayList<STATE> preds = new ArrayList<STATE>();
//		for(IncomingInternalTransition<LETTER, STATE> inTrans : internalPredecessors(cont.getState())) {
//			preds.add(inTrans.getPred());
//		}
//		for(IncomingReturnTransition<LETTER, STATE> inTrans  : returnPredecessors(cont.getState())) {
//			preds.add(inTrans.getHierPred());
//		}
//		boolean result = true;
//		for (STATE pred : preds) {
//			StateContainer<LETTER, STATE> predCont = m_States.get(pred);
//			if (predCont.getCommonEntriesComponent() != cec) {
//				if (predCont.getCommonEntriesComponent().m_BorderOut.containsKey(predCont)) {
//					Set<StateContainer<LETTER, STATE>> foreigners = 
//							predCont.getCommonEntriesComponent().m_BorderOut.get(predCont);
//					result &= foreigners.contains(cont); 
//				} else {
//					result = false;
//				}
//				assert result;
//			} else {
//				if (predCont.getCommonEntriesComponent().m_BorderOut.containsKey(predCont)) {
//					Set<StateContainer<LETTER, STATE>> foreigners = 
//							predCont.getCommonEntriesComponent().m_BorderOut.get(predCont);
//					result&= !foreigners.contains(cont);
//					assert result;
//				}
//			}
//		}
//		return result;
//	}
	
	
	
	
	

	////////////////////////////////////////////////////////////////////////////
	// Auxilliary Methods

	public static <E> boolean noElementIsNull(Collection<E> collection) {
		for (E elem : collection) {
			if (elem == null) return false;
		}
		return true;
	}
	
	private static <E> boolean isSubset(Set<E> lhs, Set<E> rhs) {
		for (E elem : lhs) {
			if (!rhs.contains(elem)) {
				return false;
			}
		}
		return true;
	}
	
	@Override
	public String toString() {
		return (new AtsDefinitionPrinter<String,String>("nwa", this)).getDefinitionAsString();
	}

}
