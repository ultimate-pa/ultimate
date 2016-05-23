/*
 * Copyright (C) 2016 Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 * Copyright (C) 2016 University of Freiburg
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
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.Collection;
import java.util.Collections;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

/**
 * 
 * @author Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 */
public class QuotientNwaConstructor<LETTER, STATE>  {
	
	private final AutomataLibraryServices m_Services;
	private final StateFactory<STATE> m_StateFactory;
	private final INestedWordAutomaton<LETTER, STATE> m_Operand;
	private final UnionFind<STATE> m_UnionFind;
	private final NestedWordAutomaton<LETTER, STATE> m_Result;

	public QuotientNwaConstructor(AutomataLibraryServices services, StateFactory<STATE> stateFactory,
			INestedWordAutomaton<LETTER, STATE> operand, UnionFind<STATE> unionFind) {
		m_Services = services;
		m_StateFactory = stateFactory;
		m_Operand = operand;
		m_UnionFind = unionFind;
		m_Result = new NestedWordAutomaton<>(m_Services, 
				m_Operand.getInternalAlphabet(), m_Operand.getCallAlphabet(), 
				m_Operand.getReturnAlphabet(), m_StateFactory);
		
		final ResultStateConstructor resStateConstructor = new ResultStateConstructor();
		for (STATE inputState : m_Operand.getStates()) {
			final STATE resultState = resStateConstructor.getOrConstructResultState(inputState); 
			for (OutgoingInternalTransition<LETTER, STATE> trans : m_Operand.internalSuccessors(inputState)) {
				final STATE resultSucc = resStateConstructor.getOrConstructResultState(trans.getSucc());
				m_Result.addInternalTransition(resultState, trans.getLetter(), resultSucc);
			}
			
			for (OutgoingCallTransition<LETTER, STATE> trans : m_Operand.callSuccessors(inputState)) {
				final STATE resultSucc = resStateConstructor.getOrConstructResultState(trans.getSucc());
				m_Result.addCallTransition(resultState, trans.getLetter(), resultSucc);
			}
			
			for (OutgoingReturnTransition<LETTER, STATE> trans : m_Operand.returnSuccessors(inputState)) {
				final STATE resultSucc = resStateConstructor.getOrConstructResultState(trans.getSucc());
				final STATE resultHierPred = resStateConstructor.getOrConstructResultState(trans.getHierPred());
				m_Result.addReturnTransition(resultState, resultHierPred, trans.getLetter(), resultSucc);
			}
		}

	}
	
	private class ResultStateConstructor {
		private final ConstructionCache<STATE, STATE> m_ConstructionCache;
		
		public ResultStateConstructor() {
			final IValueConstruction<STATE, STATE> valueConstruction = new IValueConstruction<STATE, STATE>() {
				@Override
				public STATE constructValue(STATE inputState) {
					final STATE representative = m_UnionFind.find(inputState);
					if (representative != inputState && representative != null) {
						throw new IllegalArgumentException("must be representative or null");
					}
					final STATE resultState;
					final boolean isInitial;
					final boolean isFinal;
					if (representative == null) {
						 resultState = m_StateFactory.minimize(Collections.singleton(inputState));
						 isInitial = m_Operand.isInitial(inputState);
						 isFinal = m_Operand.isFinal(inputState);
					} else {
						final Collection<STATE> equivalenceClass = m_UnionFind.getEquivalenceClassMembers(representative);
						resultState = m_StateFactory.minimize(equivalenceClass);
						final Predicate<STATE> pInitial = (s -> m_Operand.isInitial(s));
						isInitial = equivalenceClass.stream().anyMatch(pInitial);
						final Predicate<STATE> pFinal = (s -> m_Operand.isFinal(s));
						isFinal = equivalenceClass.stream().anyMatch(pFinal);
					}
					m_Result.addState(isInitial, isFinal, resultState);
					return resultState;
				}
			};
			m_ConstructionCache = new ConstructionCache<>(valueConstruction);
		}
		
		public STATE getOrConstructResultState(STATE inputState) {
			assert m_Operand.getStates().contains(inputState) : "no input state";
			STATE inputRepresentative = m_UnionFind.find(inputState);
			if (inputRepresentative == null) {
				inputRepresentative = inputState;
			}
			return m_ConstructionCache.getOrConstuct(inputRepresentative);
		}
	}
	

	public NestedWordAutomaton<LETTER, STATE> getResult() {
		return m_Result;
	}

}
