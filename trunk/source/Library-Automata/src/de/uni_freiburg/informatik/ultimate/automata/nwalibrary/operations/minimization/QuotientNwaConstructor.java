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
 * Constructs the quotient for a given NWA and an equivalence relation on its
 * states.
 * The equivalence relation has to be given as a {@link UnionFind} data 
 * structure.
 * @author Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 */
public class QuotientNwaConstructor<LETTER, STATE>  {
	
	private final AutomataLibraryServices mServices;
	private final StateFactory<STATE> mStateFactory;
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final UnionFind<STATE> mUnionFind;
	private final NestedWordAutomaton<LETTER, STATE> mResult;

	public QuotientNwaConstructor(AutomataLibraryServices services, StateFactory<STATE> stateFactory,
			INestedWordAutomaton<LETTER, STATE> operand, UnionFind<STATE> unionFind) {
		mServices = services;
		mStateFactory = stateFactory;
		mOperand = operand;
		mUnionFind = unionFind;
		mResult = new NestedWordAutomaton<>(mServices, 
				mOperand.getInternalAlphabet(), mOperand.getCallAlphabet(), 
				mOperand.getReturnAlphabet(), mStateFactory);
		
		final ResultStateConstructor resStateConstructor = new ResultStateConstructor();
		for (final STATE inputState : mOperand.getStates()) {
			final STATE resultState = resStateConstructor.getOrConstructResultState(inputState); 
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(inputState)) {
				final STATE resultSucc = resStateConstructor.getOrConstructResultState(trans.getSucc());
				mResult.addInternalTransition(resultState, trans.getLetter(), resultSucc);
			}
			
			for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(inputState)) {
				final STATE resultSucc = resStateConstructor.getOrConstructResultState(trans.getSucc());
				mResult.addCallTransition(resultState, trans.getLetter(), resultSucc);
			}
			
			for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(inputState)) {
				final STATE resultSucc = resStateConstructor.getOrConstructResultState(trans.getSucc());
				final STATE resultHierPred = resStateConstructor.getOrConstructResultState(trans.getHierPred());
				mResult.addReturnTransition(resultState, resultHierPred, trans.getLetter(), resultSucc);
			}
		}

	}
	
	private class ResultStateConstructor {
		private final ConstructionCache<STATE, STATE> mConstructionCache;
		
		public ResultStateConstructor() {
			final IValueConstruction<STATE, STATE> valueConstruction = new IValueConstruction<STATE, STATE>() {
				@Override
				public STATE constructValue(STATE inputState) {
					final STATE representative = mUnionFind.find(inputState);
					if (representative != inputState && representative != null) {
						throw new IllegalArgumentException("must be representative or null");
					}
					final STATE resultState;
					final boolean isInitial;
					final boolean isFinal;
					if (representative == null) {
						 resultState = mStateFactory.minimize(Collections.singleton(inputState));
						 isInitial = mOperand.isInitial(inputState);
						 isFinal = mOperand.isFinal(inputState);
					} else {
						final Collection<STATE> equivalenceClass = mUnionFind.getEquivalenceClassMembers(representative);
						resultState = mStateFactory.minimize(equivalenceClass);
						final Predicate<STATE> pInitial = (s -> mOperand.isInitial(s));
						isInitial = equivalenceClass.stream().anyMatch(pInitial);
						final Predicate<STATE> pFinal = (s -> mOperand.isFinal(s));
						isFinal = equivalenceClass.stream().anyMatch(pFinal);
					}
					mResult.addState(isInitial, isFinal, resultState);
					return resultState;
				}
			};
			mConstructionCache = new ConstructionCache<>(valueConstruction);
		}
		
		public STATE getOrConstructResultState(STATE inputState) {
			assert mOperand.getStates().contains(inputState) : "no input state";
			STATE inputRepresentative = mUnionFind.find(inputState);
			if (inputRepresentative == null) {
				inputRepresentative = inputState;
			}
			return mConstructionCache.getOrConstuct(inputRepresentative);
		}
	}
	

	public NestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

}
