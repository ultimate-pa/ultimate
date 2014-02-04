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
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;



public abstract class AbstractIntersect<LETTER,STATE> extends DoubleDeckerBuilder<LETTER,STATE>
							implements IOperation<LETTER, STATE> {

	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final INestedWordAutomatonOldApi<LETTER,STATE> m_FstNwa;
	private final INestedWordAutomatonOldApi<LETTER,STATE> m_SndNwa;
	private final NestedWordAutomaton<LETTER,STATE> m_ResultNwa;
	private final StateFactory<STATE> m_ContentFactory;
	
	private final boolean m_Buchi;
	
	
	private final Map<STATE,STATE> m_Result2fst = 
		new HashMap<STATE,STATE>();
	private final Map<STATE,STATE> m_Result2snd = 
		new HashMap<STATE,STATE>();
	private final Map<STATE,Integer> m_Result2track = 
		new HashMap<STATE,Integer>();
	
	Map<STATE,Map<STATE,STATE>> m_Track1_fst2snd2result = 
		new HashMap<STATE,Map<STATE,STATE>>();
	Map<STATE,Map<STATE,STATE>> m_Track2_fst2snd2result = 
		new HashMap<STATE,Map<STATE,STATE>>();
	
	@Override
	public abstract String operationName();

	
	@Override
	public String startMessage() {
		if (m_Buchi) {
			return "Start buchiIntersect. First operand " + 
			m_FstNwa.sizeInformation() + ". Second operand " + 
			m_SndNwa.sizeInformation();
		}
		else {
			return "Start intersect. First operand " + 
			m_FstNwa.sizeInformation() + ". Second operand " + 
			m_SndNwa.sizeInformation();	
		}
	}

	@Override
	public String exitMessage() {
		if (m_Buchi) {
			return "Finished buchiIntersect. Result " + 
			m_TraversedNwa.sizeInformation();
		}
		else {
			return "Finished intersect. Result " + 
			m_TraversedNwa.sizeInformation();
		}
	}


	

	public AbstractIntersect(boolean buchiIntersection, boolean minimizeResult,
					 INestedWordAutomatonOldApi<LETTER,STATE> fstNwa,
					 INestedWordAutomatonOldApi<LETTER,STATE> sndNwa) throws AutomataLibraryException {
	
		m_Buchi = buchiIntersection;
		m_RemoveDeadEnds = minimizeResult;
		m_FstNwa = fstNwa;
		m_SndNwa = sndNwa;
		if (!NestedWordAutomaton.sameAlphabet(m_FstNwa, m_SndNwa)) {
			throw new AutomataLibraryException("Unable to apply operation to automata with different alphabets.");
		}

		m_ContentFactory = m_FstNwa.getStateFactory();
		s_Logger.info(startMessage());
		
		Set<LETTER> newInternals = new HashSet<LETTER>();
		newInternals.addAll(m_FstNwa.getInternalAlphabet());
		newInternals.retainAll(m_SndNwa.getInternalAlphabet());
		Set<LETTER> newCalls = new HashSet<LETTER>();
		newCalls.addAll(m_FstNwa.getCallAlphabet());
		newCalls.retainAll(m_SndNwa.getCallAlphabet());
		Set<LETTER> newReturns = new HashSet<LETTER>();
		newReturns.addAll(m_FstNwa.getReturnAlphabet());
		newReturns.retainAll(m_SndNwa.getReturnAlphabet());
		
		m_ResultNwa = new NestedWordAutomaton<LETTER,STATE>(
				newInternals, newCalls,	newReturns,	m_ContentFactory);
		super.m_TraversedNwa = (NestedWordAutomaton<LETTER,STATE>) m_ResultNwa;
		super.traverseDoubleDeckerGraph();
		s_Logger.info(exitMessage());
		
		if (m_Buchi) {
			assert (ResultChecker.buchiIntersect(m_FstNwa, m_SndNwa, m_ResultNwa));
		}
		else {
		}
	}
	
	
	
	private STATE getOrConstructOnTrack1(
						STATE fst, STATE snd, boolean isInitial) {
		Map<STATE, STATE> snd2result = m_Track1_fst2snd2result.get(fst);
		if (snd2result == null) {
			snd2result = new HashMap<STATE, STATE>();
			m_Track1_fst2snd2result.put(fst, snd2result);
		}
		STATE state = snd2result.get(snd);
		if (state == null) {
			boolean isFinal;
			if (m_Buchi) {
				isFinal = m_FstNwa.isFinal(fst);
			}
			else {
				isFinal = m_FstNwa.isFinal(fst) && m_SndNwa.isFinal(snd);
			}
			
			if (m_Buchi) {
				state = m_ContentFactory.intersectBuchi(
										fst, snd, 1);				
			}
			else {
			state= m_ContentFactory.intersection(
											fst, snd);
			}

			m_ResultNwa.addState(isInitial, isFinal, state);
			snd2result.put(snd,state);
			m_Result2fst.put(state, fst);
			m_Result2snd.put(state, snd);
			m_Result2track.put(state, 1);
		}
		return state;
	}
	
	private STATE getOrConstructOnTrack2(
						STATE fst, STATE snd) {
		Map<STATE, STATE> snd2result = m_Track2_fst2snd2result.get(fst);
		if (snd2result == null) {
			snd2result = new HashMap<STATE, STATE>();
			m_Track2_fst2snd2result.put(fst, snd2result);
		}
		STATE state = snd2result.get(snd);
		if (state == null) {
			boolean isInitial = false;
			boolean isFinal = false;
			assert (m_Buchi);
			state = m_ContentFactory.intersectBuchi(fst, snd, 2);				
			m_ResultNwa.addState(isInitial, isFinal, state);
			snd2result.put(snd,state);
			m_Result2fst.put(state, fst);
			m_Result2snd.put(state, snd);
			m_Result2track.put(state, 2);
		}
		return state;
	}
	
	
	private int getSuccTrack(int stateTrack, STATE fstState, STATE sndState) {
		int succTrack;
		if (m_Buchi) {
			if (stateTrack == 1) {
				if (m_FstNwa.isFinal(fstState)) {
					succTrack = 2;
				}
				else {
					succTrack = 1;
				}
			}
			else {
				assert(stateTrack == 2);
				if (m_SndNwa.isFinal(sndState)) {
					succTrack = 1;
				}
				else {
					succTrack = 2;
				}
			}
		}
		else {
			succTrack = 1;
		}
		return succTrack;
	}
	
	
	
	@Override
	protected Collection<STATE> getInitialStates() {
		int amount = m_FstNwa.getInitialStates().size() *
										m_SndNwa.getInitialStates().size();
		Collection<STATE> resInits = new ArrayList<STATE>(amount);
		for (STATE fstInit : m_FstNwa.getInitialStates()) {
			for (STATE sndInit : m_SndNwa.getInitialStates()) {
				STATE resInit = getOrConstructOnTrack1(fstInit, sndInit, true);
				resInits.add(resInit);
			}
		}
		return resInits;
	}
	
	

	
	@Override
	protected Collection<STATE> buildInternalSuccessors(
											DoubleDecker<STATE> doubleDecker) {
		STATE resState = doubleDecker.getUp();
		STATE fstState = m_Result2fst.get(resState);
		STATE sndState = m_Result2snd.get(resState);
		int stateTrack = m_Result2track.get(resState);
		int succTrack = getSuccTrack(stateTrack, fstState, sndState);
		Collection<STATE> resSuccs = new ArrayList<STATE>();
		for (LETTER symbol : m_FstNwa.lettersInternal(fstState)) {
			for (STATE fstSucc : m_FstNwa.succInternal(fstState,symbol)) {
				for (STATE sndSucc : m_SndNwa.succInternal(sndState,symbol)) {
					STATE resSucc;
					if (succTrack == 1) {
						resSucc = getOrConstructOnTrack1(fstSucc,sndSucc,false);
					}
					else {
						assert (succTrack == 2);
						resSucc = getOrConstructOnTrack2(fstSucc, sndSucc);
					}
					m_ResultNwa.addInternalTransition(resState, symbol, resSucc);
					resSuccs.add(resSucc);
				}
			}
		}
		return resSuccs;
	}
	
	

	@Override
	protected Collection<STATE> buildCallSuccessors(
											DoubleDecker<STATE> doubleDecker) {
		STATE resState = doubleDecker.getUp();
		STATE fstState = m_Result2fst.get(resState);
		STATE sndState = m_Result2snd.get(resState);
		int stateTrack = m_Result2track.get(resState);
		int succTrack = getSuccTrack(stateTrack, fstState, sndState);
		Collection<STATE> resSuccs = new ArrayList<STATE>();
		for (LETTER symbol : m_FstNwa.lettersCall(fstState)) {
			for (STATE fstSucc : m_FstNwa.succCall(fstState,symbol)) {
				for (STATE sndSucc : m_SndNwa.succCall(sndState,symbol)) {
					STATE resSucc;
					if (succTrack == 1) {
						resSucc = getOrConstructOnTrack1(fstSucc,sndSucc,false);
					}
					else {
						assert (succTrack == 2);
						resSucc = getOrConstructOnTrack2(fstSucc, sndSucc);
					}
					m_ResultNwa.addCallTransition(resState, symbol, resSucc);
					resSuccs.add(resSucc);
				}
			}
		}
		return resSuccs;
	}



	@Override
	protected Collection<STATE> buildReturnSuccessors(
											DoubleDecker<STATE> doubleDecker) {
		Collection<STATE> resSuccs = new ArrayList<STATE>();
		STATE resHierPre = doubleDecker.getDown();
		if (resHierPre == m_ResultNwa.getEmptyStackState()) {
			return resSuccs;
		}
		STATE fstHierPre = m_Result2fst.get(resHierPre);
		STATE sndHierPre = m_Result2snd.get(resHierPre);
		STATE resState = doubleDecker.getUp();
		STATE fstState = m_Result2fst.get(resState);
		STATE sndState = m_Result2snd.get(resState);
		int stateTrack = m_Result2track.get(resState);
		int succTrack = getSuccTrack(stateTrack, fstState, sndState);
		
		for (LETTER symbol : m_FstNwa.lettersReturn(fstState)) {
			for (STATE fstSucc : m_FstNwa.succReturn(fstState,fstHierPre,symbol)) {
				for (STATE sndSucc : m_SndNwa.succReturn(sndState,sndHierPre,symbol)) {
					STATE resSucc;
					if (succTrack == 1) {
						resSucc = getOrConstructOnTrack1(fstSucc,sndSucc,false);
					}
					else {
						assert (succTrack == 2);
						resSucc = getOrConstructOnTrack2(fstSucc, sndSucc);
					}
					m_ResultNwa.addReturnTransition(resState, resHierPre, symbol, resSucc);
					resSuccs.add(resSucc);
				}
			}
		}
		return resSuccs;
	}





}
