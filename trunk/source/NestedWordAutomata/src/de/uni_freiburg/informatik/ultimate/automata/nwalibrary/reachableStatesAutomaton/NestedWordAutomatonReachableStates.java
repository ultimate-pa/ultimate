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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.ArrayDeque;
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
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.HashRelation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval.UpDownEntry;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.StateContainer.DownStateProp;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

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
	
	enum InCaRe { INTERNAL, CALL, RETURN, SUMMARY};
	

	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as 
	 * map HierPREs -> LETTERs -> LinPREs -> SUCCs
	 * 
	 */
	private Map<STATE,Map<LETTER,Map<STATE,Set<STATE>>>> m_ReturnSummary =
			new HashMap<STATE,Map<LETTER,Map<STATE,Set<STATE>>>>();

	
	


//	private Map<StateContainer<LETTER,STATE>,Set<StateContainer<LETTER,STATE>>> m_Summaries = new HashMap<StateContainer<LETTER,STATE>,Set<StateContainer<LETTER,STATE>>>();

	private Set<LETTER> m_EmptySetOfLetters = Collections.emptySet();

	private AncestorComputation m_WithOutDeadEnds;
	private AncestorComputation m_OnlyLiveStates;
	private AcceptingSummariesComputation m_AcceptingSummaries;
	private StronglyConnectedComponents m_StronglyConnectedComponents;

	/**
	 * Construct a run for each accepting state.
	 * Use this only while developing/debugging/testing the construction
	 * of runs.
	 */
	private final static boolean m_ExtRunConstructionTesting = false;
	
	/**
	 * Construct a lasso for each accepting state/accepting summary.
	 * Use this only while developing/debugging/testing the construction
	 * of lassos.
	 */
	private final static boolean m_ExtLassoConstructionTesting = false;
	
	/**
	 * Use also other methods for lasso construction. This is only useful if
	 * you want to analyze if the lasso construction can be optimized.
	 */
	private final static boolean m_UseAlternativeLassoConstruction = false;
	

	
//	private void addSummary(StateContainer<LETTER,STATE> callPred, StateContainer<LETTER,STATE> returnSucc) {
//		Set<StateContainer<LETTER,STATE>> returnSuccs = m_Summaries.get(callPred);
//		if (returnSuccs == null) {
//			returnSuccs = new HashSet<StateContainer<LETTER,STATE>>();
//			m_Summaries.put(callPred, returnSuccs);
//		}
//		returnSuccs.add(returnSucc);
//	}
	
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
			if (m_ExtLassoConstructionTesting) {
				getOrComputeStronglyConnectedComponents().computeNestedLassoRuns(false);
				List<NestedLassoRun<LETTER, STATE>> runs = 
						getOrComputeStronglyConnectedComponents().getAllNestedLassoRuns();
				for (NestedLassoRun<LETTER, STATE> nlr : runs) {
					STATE honda = nlr.getLoop().getStateAtPosition(0);
					s_Logger.debug(new DebugMessage("Test lasso construction for honda state {0}",honda));
					assert (new BuchiAccepts<LETTER, STATE>(NestedWordAutomatonReachableStates.this, nlr.getNestedLassoWord())).getResult();
				}
				
			}
			s_Logger.info(stateContainerInformation());
//			assert (new TransitionConsitenceCheck<LETTER, STATE>(this)).consistentForAll();

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
	
	public StronglyConnectedComponents getOrComputeStronglyConnectedComponents() {
		if (m_StronglyConnectedComponents == null) {
			computeStronglyConnectedComponents();
		}
		return m_StronglyConnectedComponents;
	}
	
	StateContainer<LETTER, STATE> obtainSC(STATE state) {
		return m_States.get(state);
	}
	
	boolean isAccepting(Summary<LETTER, STATE> summary) {
		StateContainer<LETTER, STATE> callPred = summary.getHierPred();
		Set<Summary<LETTER, STATE>> summariesForHier = 
				m_AcceptingSummaries.getAcceptingSummaries().getImage(callPred);
		if (summariesForHier == null) {
			return false;
		} else {
			return summariesForHier.contains(summary);
		}
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
		m_AcceptingSummaries = new AcceptingSummariesComputation();
		m_StronglyConnectedComponents = new StronglyConnectedComponents(m_AcceptingSummaries);
	}
	
	public void computeNonLiveStates() {
		if (m_OnlyLiveStates != null) {
			return;
//			throw new AssertionError("non-live states are already computed");
		}
		if (getOrComputeStronglyConnectedComponents() == null) {
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
	
	@Override
	public boolean isDoubleDecker(STATE up, STATE down) {
		return getDownStates(up).contains(down);
	}
	

	
	
	
	////////////////////////////////////////////////////////////////////////////
	
	
	/**
	 * Compute the set of reachable doubledeckers. 
	 * Construct a state container for each reachable state, add both (state 
	 * and StateContainer) to m_States and set the reachability down state 
	 * information in the state container.  
	 *
	 */
	private class ReachableStatesComputation {
		private int m_NumberOfConstructedStates = 0;
		private final LinkedList<StateContainer<LETTER,STATE>> m_ForwardWorklist = 
				new LinkedList<StateContainer<LETTER,STATE>>();
		private final LinkedList<StateContainer<LETTER,STATE>> m_DownPropagationWorklist =
				new LinkedList<StateContainer<LETTER,STATE>>();

		ReachableStatesComputation() throws OperationCanceledException {
			addInitialStates(m_Operand.getInitialStates());

			do {
				while (!m_ForwardWorklist.isEmpty()) {
					final StateContainer<LETTER,STATE> cont = m_ForwardWorklist.remove(0);
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
			
			if (m_ExtRunConstructionTesting ) {
				for (STATE fin : getFinalStates()) {
					s_Logger.debug(new DebugMessage("Test if can find an accepting run for final state {0}",fin));
					NestedRun<LETTER,STATE> run = (new RunConstructor<LETTER, STATE>(
							NestedWordAutomatonReachableStates.this, m_States.get(fin))).constructRun();
					assert (new Accepts<LETTER, STATE>(NestedWordAutomatonReachableStates.this, run.getWord())).getResult();
				}
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
				assert (!containsCallTransition(state, trans.getLetter(), succ)) : 
					"Operand contains transition twice: " + state + trans.getSucc();
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
				assert (!containsCallTransition(state, trans.getLetter(), succ)) : 
					"Operand contains transition twice: " + state + trans.getSucc();
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
				assert (!containsReturnTransition(state, down, trans.getLetter(), succ)) : 
					"Operand contains transition twice: " + state + trans.getSucc();
				cont.addReturnOutgoing(trans);
				succCont.addReturnIncoming(
						new IncomingReturnTransition<LETTER, STATE>(cont.getState(), down, trans.getLetter()));
				addReturnSummary(state, down, trans.getLetter(), succ);
//				addSummary(downCont, succCont);
			}
			if (addedSelfloop) {
				return newDownStatesSelfloop(cont, downCont.getDownStates().keySet());
			} else {
				return null;
			}
		}


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
	/**
	 * Compute all ancestor double deckers  for a given set of states which we
	 * call the precious states. (In a dead end computation the precious states
	 * are the final states, in a non-live computation the precious states are
	 * all states of accepting SCCs).
	 * 
	 * If a state <i>up</i> can reach a precious state via a run without 
	 * pending returns, we known that all double deckers <i>(up,down)</i> can
	 * reach a precious state and <i>up</i> gets the property "allDownProp".
	 * 
	 * If a state <i>up</i> can reach a precious state only via a run with 
	 * pending calls we identify the down states such that the double decker
	 * <i>(up,down)</i> can reach a precious state. The up state gets the
	 * property "someDownProp", and the double decker gets the property 
	 * "downStateProp" (this information is stored in the state container of 
	 * <i>up</i>.
	 *
	 */
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

		AncestorComputation(HashSet<StateContainer<LETTER,STATE>> preciousStates, 
				ReachProp allDownProp, ReachProp someDownProp, DownStateProp downStateProp) {
			m_rpAllDown = allDownProp;
			m_rpSomeDown = someDownProp;
			m_DownStateProp = downStateProp;
			
			for (StateContainer<LETTER,STATE> cont : preciousStates) {
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
						if (isFinal(predCont.getState())) {
							m_AncestorsAccepting.add(predCont.getState());
						}
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
		 * reach a precious state (finals DeadEndComputation, accepting
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
	
	/**
	 * Detect which summaries are accepting. Find states q and q' such that q'
	 * is reachable from q via a run that
	 * <ul>
	 * <li> starts with a call
	 * <li> ends with a return
	 * <li> contains an accepting state
	 * </ul>
	 * The resulting map has call predecessors in its keySet and sets of return
	 * successors in its values.
	 */
	private class AcceptingSummariesComputation {
		private final ArrayDeque<StateContainer<LETTER,STATE>> m_FinAncWorklist =
				new ArrayDeque<StateContainer<LETTER,STATE>>();
		private final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> m_AcceptingSummaries = 
				new HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>>();

		public AcceptingSummariesComputation() {
			init();
			while (!m_FinAncWorklist.isEmpty()) {
				StateContainer<LETTER, STATE> cont = m_FinAncWorklist.removeFirst();
				propagateNewDownStates(cont);
			}
		}
		
		public HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> getAcceptingSummaries() {
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
					addAcceptingSummary(hierCont, cont, trans.getLetter(), succCont);
				}
			}
		}

		private void addAcceptingSummary(
				StateContainer<LETTER, STATE> callPred,
				StateContainer<LETTER, STATE> returnPred,
				LETTER letter,
				StateContainer<LETTER, STATE> returnSucc) {
			Summary<LETTER, STATE> summary = 
					new Summary<LETTER, STATE>(callPred, returnPred, letter, returnSucc);
			m_AcceptingSummaries.addPair(callPred, summary);
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
    	
		private final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> m_AcceptingSummaries;
		
		private final Set<StateContainer<LETTER, STATE>> m_AllStatesOfSccsWithoutCallAndReturn = 
				new HashSet<StateContainer<LETTER, STATE>>();
		
		private List<NestedLassoRun<LETTER, STATE>> m_NestedLassoRuns;
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

    	
        public StronglyConnectedComponents(AcceptingSummariesComputation asc) {
        	m_AcceptingSummaries = asc.getAcceptingSummaries();
        	for (STATE state : m_initialStates) {
        		StateContainer<LETTER, STATE> cont = m_States.get(state);
                if (!m_Indices.containsKey(cont)) {
                    strongconnect(cont);
                }
            }

            assert(automatonPartitionedBySCCs());
            for (SCC scc : m_Balls) {
            	if (scc.isAccepting()) {
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
        
        public void computeNestedLassoRuns(boolean onePerScc) throws OperationCanceledException {
        	if (onePerScc) {
        		throw new UnsupportedOperationException("not yet implemented");
        	}
        	assert m_NestedLassoRuns == null : "already computed";
        	m_NestedLassoRuns = new ArrayList<NestedLassoRun<LETTER,STATE>>();
            for (SCC scc : m_Balls) {
            	if (scc.isAccepting()) {
                	for (StateContainer<LETTER, STATE> fin  : scc.getAcceptingStates()) {
                		NestedLassoRun<LETTER, STATE> nlr2 = (new LassoConstructor<LETTER, STATE>(NestedWordAutomatonReachableStates.this, fin, scc)).getNestedLassoRun();
                		if (m_UseAlternativeLassoConstruction) {
                			int nlr2Size = nlr2.getStem().getLength() + nlr2.getLoop().getLength();
                			NestedLassoRun<LETTER, STATE> nlr = (new ShortestLassoExtractor<LETTER, STATE>(NestedWordAutomatonReachableStates.this, fin)).getNestedLassoRun();
                			int nlrSize = nlr.getStem().getLength() + nlr.getLoop().getLength();
                			NestedLassoRun<LETTER, STATE> nlr3 = (new LassoExtractor<LETTER, STATE>(NestedWordAutomatonReachableStates.this, fin, scc,  m_AcceptingSummaries)).getNestedLassoRun();
                			int nlr3Size = nlr3.getStem().getLength() + nlr3.getLoop().getLength();
                		}
                		m_NestedLassoRuns.add(nlr2);
                	}
                	for (StateContainer<LETTER, STATE> sumPred : scc.getAcceptingSummariesOfSCC().getDomain()) {
                		Set<Summary<LETTER, STATE>> summaries = scc.getAcceptingSummariesOfSCC().getImage(sumPred);
                		for (Summary<LETTER, STATE> summary : summaries) {
                    		NestedLassoRun<LETTER, STATE> nlr2 = (new LassoConstructor<LETTER, STATE>(NestedWordAutomatonReachableStates.this, summary, scc)).getNestedLassoRun();
                    		if (m_UseAlternativeLassoConstruction) {
                    			NestedLassoRun<LETTER, STATE> nlr = (new ShortestLassoExtractor<LETTER, STATE>(NestedWordAutomatonReachableStates.this,sumPred)).getNestedLassoRun();
                    			int nlrSize = nlr.getStem().getLength() + nlr.getLoop().getLength();
                    			int nlr2Size = nlr2.getStem().getLength() + nlr2.getLoop().getLength();
                    		}
                    		m_NestedLassoRuns.add(nlr2);
                		}
                	}
            	}
            }        	
        }
        
        public void computeShortNestedLassoRun() throws OperationCanceledException {
        	StateContainer<LETTER, STATE> lowestSerialNumber = null;
        	StateContainer<LETTER, STATE> newlowestSerialNumber = null;
        	SCC sccOfLowest = null;
			for (SCC scc : m_Balls) {
            	if (scc.isAccepting()) {
            		StateContainer<LETTER, STATE> lowestOfScc = scc.getAcceptingWithLowestSerialNumber();
            		newlowestSerialNumber = StateContainer.returnLower(lowestSerialNumber, lowestOfScc);
            		if (newlowestSerialNumber != lowestSerialNumber) {
            			lowestSerialNumber = newlowestSerialNumber;
            			sccOfLowest = scc;
            		}
            	}
            }
			NestedLassoRun<LETTER, STATE> method4 = (new LassoConstructor<LETTER, STATE>(NestedWordAutomatonReachableStates.this, lowestSerialNumber, sccOfLowest)).getNestedLassoRun();
			s_Logger.debug("Method4: stem" + method4.getStem().getLength() + " loop" + method4.getLoop().getLength());
			if (m_UseAlternativeLassoConstruction) {
				NestedLassoRun<LETTER, STATE> method0 = (new LassoExtractor<LETTER, STATE>(NestedWordAutomatonReachableStates.this, sccOfLowest.getStateWithLowestSerialNumber(), sccOfLowest,  m_AcceptingSummaries)).getNestedLassoRun();
				s_Logger.debug("Method0: stem" + method0.getStem().getLength() + " loop" + method0.getLoop().getLength());
				NestedLassoRun<LETTER, STATE> method1 = (new LassoExtractor<LETTER, STATE>(NestedWordAutomatonReachableStates.this, lowestSerialNumber, sccOfLowest,  m_AcceptingSummaries)).getNestedLassoRun();
				s_Logger.debug("Method1: stem" + method1.getStem().getLength() + " loop" + method1.getLoop().getLength());
				NestedLassoRun<LETTER, STATE> method2 = (new ShortestLassoExtractor<LETTER, STATE>(NestedWordAutomatonReachableStates.this,lowestSerialNumber)).getNestedLassoRun();
				s_Logger.debug("Method2: stem" + method2.getStem().getLength() + " loop" + method2.getLoop().getLength());
				int method0size = method0.getStem().getLength() + method0.getLoop().getLength();
				int method1size = method1.getStem().getLength() + method1.getLoop().getLength();
				int method2size = method2.getStem().getLength() + method1.getLoop().getLength();
				s_Logger.debug("Method0size" + method0size +" Method1size" + method1size + " Method2size" + method2size);
			}
			m_NestedLassoRun = method4;
        }
    
        
        
        public List<NestedLassoRun<LETTER, STATE>> getAllNestedLassoRuns() throws OperationCanceledException {
        	if (buchiIsEmpty()) {
        		return Collections.emptyList();
        	} else {
        		if (m_NestedLassoRuns == null) {
        			computeNestedLassoRuns(false);
        		}
        		return m_NestedLassoRuns;
        	}
        }
        
        public NestedLassoRun<LETTER, STATE> getNestedLassoRun() throws OperationCanceledException {
        	if (buchiIsEmpty()) {
        		return null;
        	} else {
        		if (m_NestedLassoRun == null) {
        			computeShortNestedLassoRun();
        		}
        		return m_NestedLassoRun;
        	}
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
	    	/**
	    	 * States that have an outgoing summary. The summary successor may
	    	 * could be outside of this SCC. We determine the needed set only
	    	 * if construction of this SCC is finished.
	    	 */
	    	Set<StateContainer<LETTER, STATE>> m_HasOutgoingAcceptingSum = 
	    			new HashSet<StateContainer<LETTER, STATE>>();
	    	final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>>m_AcceptingSummariesOfSCC =
	    			new HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>>();
	    	final Set<StateContainer<LETTER, STATE>> m_AllStates = 
	    			new HashSet<StateContainer<LETTER, STATE>>();
	    	/**
	    	 * State of SCC with lowest serial number.
	    	 */
	    	private StateContainer<LETTER, STATE> m_StateWithLowestSerialNumber;
	    	/**
	    	 * State of SCC with lowest serial number that is accepting or
	    	 * successor 
	    	 */
	    	private StateContainer<LETTER, STATE> m_AcceptingWithLowestSerialNumber;
	    	
	    	public void addState(StateContainer<LETTER, STATE> cont) {
	    		if (m_RootNode != null) {
	    			throw new UnsupportedOperationException(
	    					"If root node is set SCC may not be modified");
	    		}
	    		m_AllStates.add(cont);
	    		m_StateWithLowestSerialNumber = StateContainer.
	    				returnLower(m_StateWithLowestSerialNumber, cont);

	    		if (isFinal(cont.getState())) {
	    			m_AcceptingStates.add(cont);
	    			m_AcceptingWithLowestSerialNumber = StateContainer.
		    				returnLower(m_AcceptingWithLowestSerialNumber, cont);
	    		}
	    		if (m_AcceptingSummaries.getDomain().contains(cont)) {
	    			m_HasOutgoingAcceptingSum.add(cont);
	    			// if we have to update lowest is determined later
	    		}
	    	}
	    	
			public void setRootNode(StateContainer<LETTER, STATE> rootNode) {
	    		if (m_RootNode != null) {
	    			throw new UnsupportedOperationException(
	    					"If root node is set SCC may not be modified");
	    		}
				this.m_RootNode = rootNode;
				//TODO: Optimization: compute this only if there is no 
				// accepting state in SCC
				for (StateContainer<LETTER, STATE> pred : m_HasOutgoingAcceptingSum) {
	    			for (Summary<LETTER, STATE> summary : m_AcceptingSummaries.getImage(pred)) {
	    				if (m_AllStates.contains(summary.getSucc())) {
	    	    			m_AcceptingWithLowestSerialNumber = StateContainer.
	    		    				returnLower(m_AcceptingWithLowestSerialNumber, pred);
	    					m_AcceptingSummariesOfSCC.addPair(pred, summary);
	    				}
	    			}
				}
				m_HasOutgoingAcceptingSum = null;
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
			
			public HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> getAcceptingSummariesOfSCC() {
				return m_AcceptingSummariesOfSCC;
			}

			public StateContainer<LETTER, STATE> getStateWithLowestSerialNumber() {
				return m_StateWithLowestSerialNumber;
			}
			
			public boolean isAccepting() {
				return m_AcceptingWithLowestSerialNumber != null;
			}
			
			/**
			 * Returns the state with the lowest serial number that is accepting
			 * or call predecessor of an accepting summary.
			 * Returns null if no such state exists.
			 * @return 
			 */
			public StateContainer<LETTER, STATE> getAcceptingWithLowestSerialNumber() {
				return m_AcceptingWithLowestSerialNumber;
			}
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
