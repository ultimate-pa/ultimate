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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi;

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
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;



/**
 * Given two nondeterministic NWAs nwa_minuend and nwa_subtrahend a
 * DifferenceAutomatonBuilder can compute a NWA nwa_difference
 * such that nwa_difference accepts all words that are accepted by nwa_minuend
 * but not by Psi(nwa_subtrahend), i.e. 
 * L(nwa_difference) = L(nwa_minuend) \ L( Psi(nwa_subtrahend) ),
 * where Psi is a transformation of the automaton nwa_subtrahend that is defined
 * by an implementation of IStateDeterminizer.
 * 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER> Symbol. Type of the elements of the alphabet over which the
 * automata are defined. 
 * @param <STATE> Content. Type of the labels that are assigned to the states of
 * automata. In many cases you want to use String as STATE and your states are
 * labeled e.g. with "q0", "q1", ... 
 */
//TODO: Optimization for special case where subtrahend is closed under
// concatenation with Sigma^*. Use only one DeterminizedState detFin state that
// represents all final states. Each successor of detFin is detFin itself.
public class DifferenceDD<LETTER,STATE> extends DoubleDeckerBuilder<LETTER,STATE> 
							 implements IOperation<LETTER,STATE> {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	/**
	 * If set the language of the subtrahend is closed under concatenation with
	 * sigma star. This means for determinized subtrahends: Once in the final
	 * state you can never escape the final states. Hence the result can omit
	 * all states where the subtrahend is final. 
	 */
	private final boolean m_subtrahendSigmaStarClosed;
	
	private final INestedWordAutomatonOldApi<LETTER,STATE> minuend;
	private final INestedWordAutomatonOldApi<LETTER,STATE> subtrahend;
	
	private final IStateDeterminizer<LETTER,STATE> stateDeterminizer;
	
	/**
	 * Maps a DifferenceState to its representative in the resulting automaton.
	 */
	private Map<DifferenceState<LETTER,STATE>,STATE> diff2res =
		new HashMap<DifferenceState<LETTER,STATE>, STATE>();
	
	/**
	 * Maps a state in resulting automaton to the DifferenceState for which it
	 * was created.
	 */
	private final Map<STATE,DifferenceState<LETTER,STATE>> res2diff =
		new HashMap<STATE, DifferenceState<LETTER,STATE>>();
	
	/**
	 * StateFactory used for the construction of new states. This is _NOT_ the
	 * state factory relayed to the new automaton.
	 * Necessary because the Automizer needs a special StateFactory during
	 * abstraction refinement (for computation of HoareAnnotation).
	 */
	private final StateFactory<STATE> m_StateFactoryConstruction;
	
	
//	private INestedWordAutomaton<LETTER,DeterminizedState<LETTER,STATE>> 
//													m_DeterminizedSubtrahend;

	
	
	int m_InternalSuccs = 0;
	int m_InternalSuccsCache = 0;
	int m_CallSuccs = 0;
	int m_CallSuccsCache = 0;
	int m_ReturnSuccs = 0;
	int m_ReturnSuccsCache = 0;
	int m_Unnecessary = 0;
	
	
	Map<DeterminizedState<LETTER,STATE>,DeterminizedState<LETTER,STATE>> m_DetStateCache =
		new HashMap<DeterminizedState<LETTER,STATE>,DeterminizedState<LETTER,STATE>>();
	
	Map<DeterminizedState<LETTER,STATE>,Map<LETTER,DeterminizedState<LETTER,STATE>>>	m_InternalSuccessorCache =
	new HashMap<DeterminizedState<LETTER,STATE>,Map<LETTER,DeterminizedState<LETTER,STATE>>>();
	
	Map<DeterminizedState<LETTER,STATE>,Map<LETTER,DeterminizedState<LETTER,STATE>>>	m_CallSuccessorCache =
		new HashMap<DeterminizedState<LETTER,STATE>,Map<LETTER,DeterminizedState<LETTER,STATE>>>();
	
	Map<DeterminizedState<LETTER,STATE>,Map<DeterminizedState<LETTER,STATE>,Map<LETTER,DeterminizedState<LETTER,STATE>>>> 
	 m_ReturnSuccessorCache = new HashMap<DeterminizedState<LETTER,STATE>,
		Map<DeterminizedState<LETTER,STATE>,Map<LETTER,DeterminizedState<LETTER,STATE>>>>();

	private STATE subtrahendAuxilliaryEmptyStackState;
	
	
	@Override
	public String operationName() {
		return "difference";
	}
	
	@Override
	public String startMessage() {
			return "Start " + operationName() + ". Minuend " + 
			minuend.sizeInformation() + ". Subtrahend " + 
			subtrahend.sizeInformation();	
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
		m_TraversedNwa.sizeInformation() + ". Max degree of Nondeterminism is " + 
		stateDeterminizer.getMaxDegreeOfNondeterminism() +
		". DeterminizedStates: " + m_DetStateCache.size();
	}
	
	
	
	private DeterminizedState<LETTER,STATE> internalSuccessorCache(
			DeterminizedState<LETTER,STATE>  state,
			LETTER symbol) {
		Map<LETTER, DeterminizedState<LETTER,STATE>> symbol2succ = 
			m_InternalSuccessorCache.get(state);
		if (symbol2succ == null) {
			return null;
		}
		return symbol2succ.get(symbol);
	}
	
	private void putInternalSuccessorCache(
			DeterminizedState<LETTER,STATE>  state,
			LETTER symbol,
			DeterminizedState<LETTER,STATE>  succ) {
		Map<LETTER, DeterminizedState<LETTER,STATE>> symbol2succ = 
			m_InternalSuccessorCache.get(state);
		if (symbol2succ == null) {
			symbol2succ = new HashMap<LETTER,DeterminizedState<LETTER,STATE>>();
			m_InternalSuccessorCache.put(state, symbol2succ);
		}
		symbol2succ.put(symbol, succ);	
	}
	
	
	
	private DeterminizedState<LETTER,STATE> callSuccessorCache(
			DeterminizedState<LETTER,STATE>  state,
			LETTER symbol) {
		Map<LETTER, DeterminizedState<LETTER,STATE>> symbol2succ = 
			m_CallSuccessorCache.get(state);
		if (symbol2succ == null) {
			return null;
		}
		return symbol2succ.get(symbol);
	}
	
	private void putCallSuccessorCache(
			DeterminizedState<LETTER,STATE>  state,
			LETTER symbol,
			DeterminizedState<LETTER,STATE>  succ) {
		Map<LETTER, DeterminizedState<LETTER,STATE>> symbol2succ = 
			m_CallSuccessorCache.get(state);
		if (symbol2succ == null) {
			symbol2succ = new HashMap<LETTER,DeterminizedState<LETTER,STATE>>();
			m_CallSuccessorCache.put(state, symbol2succ);
		}
		symbol2succ.put(symbol, succ);	
	}
	
	private DeterminizedState<LETTER,STATE> returnSuccessorCache(
			DeterminizedState<LETTER,STATE>  state,
			DeterminizedState<LETTER,STATE> linPred,
			LETTER symbol) {
		Map<DeterminizedState<LETTER,STATE>,Map<LETTER, DeterminizedState<LETTER,STATE>>> linPred2symbol2succ =
			m_ReturnSuccessorCache.get(linPred);
		if (linPred2symbol2succ == null) {
			return null;
		}
		Map<LETTER, DeterminizedState<LETTER,STATE>> symbol2succ = 
			linPred2symbol2succ.get(state);
		if (symbol2succ == null) {
			return null;
		}
		return symbol2succ.get(symbol);
	}
	
	private void putReturnSuccessorCache(
			DeterminizedState<LETTER,STATE>  state,
			DeterminizedState<LETTER,STATE> linPred,
			LETTER symbol,
			DeterminizedState<LETTER,STATE>  succ) {
		Map<DeterminizedState<LETTER,STATE>,Map<LETTER, DeterminizedState<LETTER,STATE>>> linPred2symbol2succ =
			m_ReturnSuccessorCache.get(linPred);
		if (linPred2symbol2succ == null) {
			linPred2symbol2succ = 
				new HashMap<DeterminizedState<LETTER,STATE>,Map<LETTER, DeterminizedState<LETTER,STATE>>>();
			m_ReturnSuccessorCache.put(linPred, linPred2symbol2succ);
		}
		Map<LETTER, DeterminizedState<LETTER,STATE>> symbol2succ = 
			linPred2symbol2succ.get(state);
		if (symbol2succ == null) {
			symbol2succ = new HashMap<LETTER,DeterminizedState<LETTER,STATE>>();
			linPred2symbol2succ.put(state, symbol2succ);
		}
		symbol2succ.put(symbol, succ);	
	}
	
	
	
	
	
	public DifferenceDD(
			INestedWordAutomatonOldApi<LETTER,STATE> minuend,
			INestedWordAutomatonOldApi<LETTER,STATE> subtrahend,
			IStateDeterminizer<LETTER,STATE> stateDeterminizer,
			StateFactory<STATE> stateFactory,
			boolean removeDeadEnds,
			boolean subtrahendSigmaStarClosed) throws AutomataLibraryException {
		this.m_subtrahendSigmaStarClosed = subtrahendSigmaStarClosed;
		m_StateFactoryConstruction = stateFactory;
		this.minuend = minuend;
		this.subtrahend = subtrahend;
		if (!NestedWordAutomaton.sameAlphabet(this.minuend, this.subtrahend)) {
			throw new AutomataLibraryException("Unable to apply operation to automata with different alphabets.");
		}
		s_Logger.info(startMessage());
		this.subtrahendAuxilliaryEmptyStackState = 
			subtrahend.getEmptyStackState();
		this.stateDeterminizer = stateDeterminizer;
		super.m_TraversedNwa = new DoubleDeckerAutomaton<LETTER,STATE>(
				minuend.getInternalAlphabet(),
				minuend.getCallAlphabet(),
				minuend.getReturnAlphabet(),
				minuend.getStateFactory());
		super.m_RemoveDeadEnds = removeDeadEnds;
		
//		m_DeterminizedSubtrahend = 
//			new NestedWordAutomaton<LETTER,DeterminizedState<LETTER,STATE>>(
//					minuend.getInternalAlphabet(), 
//					minuend.getCallAlphabet(), 
//					minuend.getReturnAlphabet(), 
//					null);
		traverseDoubleDeckerGraph();
		((DoubleDeckerAutomaton<LETTER,STATE>) super.m_TraversedNwa).setUp2Down(getUp2DownMapping());
		s_Logger.info(exitMessage());
		s_Logger.info("Computed internal successors:" + m_InternalSuccs);
		s_Logger.info("Internal successors via cache:" + m_InternalSuccsCache);
		s_Logger.info("Computed call successors:" + m_CallSuccs);
		s_Logger.info("Call successors via cache:" + m_CallSuccsCache);
		s_Logger.info("Computed return successors:" + m_ReturnSuccs);
		s_Logger.info("Return successors via cache:" + m_ReturnSuccsCache);
		s_Logger.info(m_Unnecessary + " times subtrahend state of successor " +
				"was accepting (use sigma star concat closure?)");
	}
	
	public DifferenceDD(StateFactory<STATE> stateFactory,
			INestedWordAutomatonOldApi<LETTER,STATE> minuend,
			INestedWordAutomatonOldApi<LETTER,STATE> subtrahend) throws AutomataLibraryException {
		this.m_subtrahendSigmaStarClosed = false;
		m_StateFactoryConstruction = minuend.getStateFactory();
		this.minuend = minuend;
		this.subtrahend = subtrahend;
		if (!NestedWordAutomaton.sameAlphabet(this.minuend, this.subtrahend)) {
			throw new AutomataLibraryException("Unable to apply operation to automata with different alphabets.");
		}
		s_Logger.info(startMessage());
		this.subtrahendAuxilliaryEmptyStackState = 
			subtrahend.getEmptyStackState();
		this.stateDeterminizer =
			new PowersetDeterminizer<LETTER,STATE>(subtrahend, true, stateFactory);
		super.m_TraversedNwa = new DoubleDeckerAutomaton<LETTER,STATE>(
				minuend.getInternalAlphabet(),
				minuend.getCallAlphabet(),
				minuend.getReturnAlphabet(),
				minuend.getStateFactory());
		super.m_RemoveDeadEnds = false;
		
		Set<LETTER> newInternals = new HashSet<LETTER>();
		newInternals.addAll(minuend.getInternalAlphabet());
		newInternals.retainAll(subtrahend.getInternalAlphabet());
		Set<LETTER> newCalls = new HashSet<LETTER>();
		newCalls.addAll(minuend.getCallAlphabet());
		newCalls.retainAll(subtrahend.getCallAlphabet());
		Set<LETTER> newReturns = new HashSet<LETTER>();
		newReturns.addAll(minuend.getReturnAlphabet());
		newReturns.retainAll(subtrahend.getReturnAlphabet());
		
//		m_DeterminizedSubtrahend = 
//			new NestedWordAutomaton<LETTER,DeterminizedState<LETTER,STATE>>(
//					minuend.getInternalAlphabet(), 
//					minuend.getCallAlphabet(), 
//					minuend.getReturnAlphabet(), 
//					null);
		traverseDoubleDeckerGraph();
		((DoubleDeckerAutomaton<LETTER,STATE>) super.m_TraversedNwa).setUp2Down(getUp2DownMapping());
		s_Logger.info(exitMessage());
	}

	
	
	
	
	
	

	@Override
	protected Collection<STATE> getInitialStates() {
		ArrayList<STATE> resInitials = 
			new ArrayList<STATE>(subtrahend.getInitialStates().size());
		DeterminizedState<LETTER,STATE> detState = stateDeterminizer.initialState();
		m_DetStateCache.put(detState, detState);
		for (STATE minuState : minuend.getInitialStates()) {
			boolean isFinal = minuend.isFinal(minuState) &&
											!detState.containsFinal();
			DifferenceState<LETTER,STATE> diffState = 
				new DifferenceState<LETTER,STATE>(minuState, detState, isFinal);
			STATE resState = m_StateFactoryConstruction.intersection(
					diffState.getMinuendState(), 
					stateDeterminizer.getState(diffState.getSubtrahendDeterminizedState()));
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addState(true, diffState.isFinal(), resState);
			diff2res.put(diffState,resState);
			res2diff.put(resState, diffState);
			resInitials.add(resState);
		}
		return resInitials;
	}


	
	@Override
	protected Collection<STATE> buildInternalSuccessors(
											DoubleDecker<STATE> doubleDecker) {
		List<STATE> resInternalSuccessors = new LinkedList<STATE>();
		STATE resState = doubleDecker.getUp();
		DifferenceState<LETTER,STATE> diffState = res2diff.get(resState);
		STATE minuState = 
			diffState.getMinuendState();
		DeterminizedState<LETTER,STATE> detState = 
			diffState.getSubtrahendDeterminizedState();
				
		for (LETTER symbol : minuend.lettersInternal(minuState)) {
			if (!subtrahend.getInternalAlphabet().contains(symbol)) {
				continue;
			}
			DeterminizedState<LETTER,STATE> detSucc = 
									internalSuccessorCache(detState, symbol);
			if (detState.containsFinal()) m_Unnecessary++; 
			if (detSucc == null) {
				m_InternalSuccs++;
				detSucc = stateDeterminizer.internalSuccessor(detState, symbol);
				if (m_DetStateCache.containsKey(detSucc)) {
					detSucc = m_DetStateCache.get(detSucc);
				}
				else {
					m_DetStateCache.put(detSucc, detSucc);
				}
				putInternalSuccessorCache(detState, symbol, detSucc);
			}
			else {
				m_InternalSuccsCache++;
			}	
			for (STATE minuSucc : minuend.succInternal(minuState, symbol)) {
				boolean isFinal = minuend.isFinal(minuSucc) &&
						!detSucc.containsFinal();
				DifferenceState<LETTER,STATE> diffSucc = 
						new DifferenceState<LETTER,STATE>(minuSucc, detSucc, isFinal);
				STATE resSucc = getResState(diffSucc);
				((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addInternalTransition(resState, symbol, resSucc);
				resInternalSuccessors.add(resSucc);
			}
		}
		return resInternalSuccessors;
	}







	@Override
	protected Collection<STATE> buildCallSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		List<STATE> resCallSuccessors = new LinkedList<STATE>();
		STATE resState = doubleDecker.getUp();
		DifferenceState<LETTER,STATE> diffState = res2diff.get(resState);
		STATE minuState = 
			diffState.getMinuendState();
		DeterminizedState<LETTER,STATE> detState = 
			diffState.getSubtrahendDeterminizedState(); 
		
		for (LETTER symbol : minuend.lettersCall(minuState)) {
			if (!subtrahend.getCallAlphabet().contains(symbol)) {
				continue;
			}
			DeterminizedState<LETTER,STATE> detSucc = 
									callSuccessorCache(detState, symbol);
			if (detState.containsFinal()) m_Unnecessary++;
			if (detSucc == null) {
				m_CallSuccs++;
				detSucc = stateDeterminizer.callSuccessor(detState, symbol);
				if (m_DetStateCache.containsKey(detSucc)) {
					detSucc = m_DetStateCache.get(detSucc);
				}
				else {
					m_DetStateCache.put(detSucc, detSucc);
				}
				putCallSuccessorCache(detState, symbol, detSucc);
			}
			else {
				m_CallSuccsCache++;
			}
			for (STATE minuSucc : minuend.succCall(minuState, symbol)) {
				if (m_subtrahendSigmaStarClosed && detSucc.containsFinal()) {
					continue;
				}
				boolean isFinal = minuend.isFinal(minuSucc) &&
						!detSucc.containsFinal();
				DifferenceState<LETTER,STATE> diffSucc = 
						new DifferenceState<LETTER,STATE>(minuSucc, detSucc, isFinal);
				STATE resSucc = getResState(diffSucc);
				((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addCallTransition(resState, symbol, resSucc);
				resCallSuccessors.add(resSucc);
			}
		}
		return resCallSuccessors;
	}









	@Override
	protected Collection<STATE> buildReturnSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		List<STATE> resReturnSuccessors = new LinkedList<STATE>();
		STATE resState = doubleDecker.getUp();
		DifferenceState<LETTER,STATE> diffState = res2diff.get(resState);
		STATE minuState = 
			diffState.getMinuendState();
		DeterminizedState<LETTER,STATE> detState = 
			diffState.getSubtrahendDeterminizedState(); 
		
		STATE resLinPred = doubleDecker.getDown();
		if (resLinPred == m_TraversedNwa.getEmptyStackState()) {
			return resReturnSuccessors;
		}
		

		
		DifferenceState<LETTER,STATE> diffLinPred = res2diff.get(resLinPred);
		STATE minuLinPred = diffLinPred.getMinuendState();
		
		DeterminizedState<LETTER,STATE> detLinPred = 
			diffLinPred.getSubtrahendDeterminizedState();
		
		for (LETTER symbol : minuend.lettersReturn(minuState)) {
			
			Iterable<STATE> minuSuccs = minuend.succReturn(minuState, minuLinPred, symbol);
			
			// do nothing if there will be no successor difference state
			if (!minuSuccs.iterator().hasNext()) continue;
			
			if (!subtrahend.getReturnAlphabet().contains(symbol)) continue;
			
			DeterminizedState<LETTER,STATE> detSucc = 
							returnSuccessorCache(detState, detLinPred, symbol);
			if (detState.containsFinal()) m_Unnecessary++;
			if (detSucc == null) {
				m_ReturnSuccs++;
				detSucc = stateDeterminizer.returnSuccessor(
												detState, detLinPred, symbol);
//				s_Logger.debug("Successor of state " + detState + " symbol " +
//						symbol + " linPred " + detLinPred + " is " + detSucc);
				
				if (m_DetStateCache.containsKey(detSucc)) {
					detSucc = m_DetStateCache.get(detSucc);
				}
				else {
					m_DetStateCache.put(detSucc, detSucc);
				}
				putReturnSuccessorCache(detState, detLinPred, symbol, detSucc);
			}
			else {
				m_ReturnSuccsCache++;
			}			
			
			for (STATE minuSucc : minuSuccs) {
				boolean isFinal = minuend.isFinal(minuSucc) &&
											!detSucc.containsFinal();
				DifferenceState<LETTER,STATE> diffSucc = 
					new DifferenceState<LETTER,STATE>(minuSucc, detSucc, isFinal);
				STATE resSucc = getResState(diffSucc);
				((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addReturnTransition(
										resState, resLinPred, symbol, resSucc);
				resReturnSuccessors.add(resSucc);
			}
		}
		return resReturnSuccessors;
	}




	
	
	/**
	 * Get the state in the resulting automaton that represents a
	 * DifferenceState. If this state in the resulting automaton does not exist
	 * yet, construct it.
	 */
	STATE getResState(DifferenceState<LETTER,STATE> diffState) {
		if (diff2res.containsKey(diffState)) {
			return diff2res.get(diffState);
		}
		else {
			STATE resState = m_StateFactoryConstruction.intersection(
					diffState.getMinuendState(),
					stateDeterminizer.getState(diffState.getSubtrahendDeterminizedState()));
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addState(false, diffState.isFinal(), resState);
			diff2res.put(diffState,resState);
			res2diff.put(resState,diffState);
			return resState;
		}
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		boolean correct = true;
		if (stateDeterminizer instanceof PowersetDeterminizer) {
			s_Logger.info("Start testing correctness of " + operationName());

			INestedWordAutomatonOldApi<LETTER,STATE> resultSadd = (new DifferenceSadd<LETTER,STATE>(stateFactory, minuend, subtrahend)).getResult();
			correct &= (ResultChecker.nwaLanguageInclusion(resultSadd, m_TraversedNwa, stateFactory) == null);
			correct &= (ResultChecker.nwaLanguageInclusion(m_TraversedNwa, resultSadd, stateFactory) == null);
			if (!correct) {
			ResultChecker.writeToFileIfPreferred(operationName() + "Failed", "", minuend,subtrahend);
			}
			s_Logger.info("Finished testing correctness of " + operationName());
		} else {
			s_Logger.warn("Unable to test correctness if state determinzier is not the PowersetDeterminizer.");
		}
		return correct;
	}


	
	






	
}
