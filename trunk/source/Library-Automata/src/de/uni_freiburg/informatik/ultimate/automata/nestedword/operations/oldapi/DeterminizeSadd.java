/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsIncluded;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class DeterminizeSadd<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	private final Map<Macrostate, STATE> mMacrostate2detState =
			new HashMap<Macrostate, STATE>();
	private final Map<STATE, Macrostate> mDetState2macrostate =
			new HashMap<STATE, Macrostate>();
	private final Map<STATE, Set<STATE>> mSummary =
			new HashMap<STATE, Set<STATE>>();
	private final STATE mAuxiliaryEmptyStackState;
	private final INestedWordAutomatonSimple<LETTER, STATE> mOperand;
	private final NestedWordAutomaton<LETTER, STATE> mResult;
	
	private final List<StatePair> mQueue = new LinkedList<StatePair>();
	
	// set of pairs that has been visited. The first state of the pair can be any automaton
	// state, the second state is a state that has an outgoing call transition.
	private final Map<STATE, Set<STATE>> mVisited =
			new HashMap<STATE, Set<STATE>>();
			
	public DeterminizeSadd(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mOperand = nwa;
		mLogger.info(startMessage());
		mResult = new NestedWordAutomaton<LETTER, STATE>(
				mServices,
				mOperand.getInternalAlphabet(),
				mOperand.getCallAlphabet(),
				mOperand.getReturnAlphabet(),
				mOperand.getStateFactory());
		mAuxiliaryEmptyStackState = mOperand.getEmptyStackState();
		determinize();
		mLogger.info(exitMessage());
	}
	
	@Override
	public String operationName() {
		return "determinizeSadd";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand "
				+ mOperand.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result "
				+ mResult.sizeInformation();
	}
	
	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}
	
	public boolean wasVisited(final STATE state, final STATE callerState) {
		final Set<STATE> callerStates = mVisited.get(state);
		if (callerStates == null) {
			return false;
		} else {
			return callerStates.contains(callerState);
		}
	}
	
	public void markVisited(final STATE state, final STATE callerState) {
		Set<STATE> callerStates = mVisited.get(state);
		if (callerStates == null) {
			callerStates = new HashSet<STATE>();
			mVisited.put(state, callerStates);
		}
		callerStates.add(callerState);
	}
	
	public void addSummary(final STATE summaryPred, final STATE summarySucc) {
		Set<STATE> summarySuccessors = mSummary.get(summaryPred);
		if (summarySuccessors == null) {
			summarySuccessors = new HashSet<STATE>();
			mSummary.put(summaryPred, summarySuccessors);
		}
		summarySuccessors.add(summarySucc);
	}
	
	public void enqueueAndMark(final STATE state, final STATE callerState) {
		if (!wasVisited(state, callerState)) {
			markVisited(state, callerState);
			final StatePair statePair = new StatePair(state, callerState);
			mQueue.add(statePair);
		}
	}
	
	private Set<STATE> getKnownCallerStates(final STATE state) {
		final Set<STATE> callerStates = mVisited.get(state);
		if (callerStates == null) {
			return new HashSet<STATE>(0);
		} else {
			return callerStates;
		}
	}
	
	private void determinize() {
		mLogger.debug("Starting determinizeSadd. Operand " + mOperand.sizeInformation());
		final Macrostate initialMacroState = new Macrostate();
		
		for (final STATE state : mOperand.getInitialStates()) {
			initialMacroState.addPair(state, mAuxiliaryEmptyStackState);
		}
		final STATE initialDetState = initialMacroState.getContent();
		mResult.addState(true, initialMacroState.mIsFinal, initialDetState);
		mMacrostate2detState.put(initialMacroState, initialDetState);
		mDetState2macrostate.put(initialDetState, initialMacroState);
		enqueueAndMark(initialDetState, mAuxiliaryEmptyStackState);
		
		while (!mQueue.isEmpty()) {
			final StatePair statePair = mQueue.remove(0);
//			mLogger.debug("Processing: "+ statePair);
			processStatePair(statePair);
			if (mSummary.containsKey(statePair.mState)) {
				for (final STATE summarySucc : mSummary.get(statePair.mState)) {
					enqueueAndMark(summarySucc, statePair.mCallerState);
				}
				
			}
		}
		assert mResult.isDeterministic();
	}
	
//	private void processSummary(IState<LETTER,STATE> summaryPred, IState<LETTER,STATE> summaryPredCaller)
	
	private void processStatePair(final StatePair statePair) {
		final STATE detState = statePair.mState;
		final Macrostate macrostate = mDetState2macrostate.get(detState);
		
		final Set<LETTER> symbolsInternal = new HashSet<LETTER>();
		for (final STATE state : macrostate.getStates()) {
			symbolsInternal.addAll(mOperand.lettersInternal(state));
		}
		for (final LETTER symbol : symbolsInternal) {
			final Macrostate succMacrostate = internalSuccMacrostate(macrostate, symbol);
			STATE succDetState = mMacrostate2detState.get(succMacrostate);
			if (succDetState == null) {
				succDetState = succMacrostate.getContent();
				mResult.addState(false, succMacrostate.mIsFinal, succDetState);
				mMacrostate2detState.put(succMacrostate, succDetState);
				mDetState2macrostate.put(succDetState, succMacrostate);
			}
			mResult.addInternalTransition(detState, symbol, succDetState);
			enqueueAndMark(succDetState, statePair.mCallerState);
		}
		
		final Set<LETTER> symbolsCall = new HashSet<LETTER>();
		for (final STATE state : macrostate.getStates()) {
			symbolsCall.addAll(mOperand.lettersCall(state));
		}
		for (final LETTER symbol : symbolsCall) {
			final Macrostate succMacrostate = callSuccMacrostate(macrostate, symbol);
			STATE succDetState = mMacrostate2detState.get(succMacrostate);
			if (succDetState == null) {
				succDetState = succMacrostate.getContent();
				mResult.addState(false, succMacrostate.mIsFinal, succDetState);
				mMacrostate2detState.put(succMacrostate, succDetState);
				mDetState2macrostate.put(succDetState, succMacrostate);
			}
			mResult.addCallTransition(detState, symbol, succDetState);
			enqueueAndMark(succDetState, detState);
		}
		
		final STATE detLinPred = statePair.mCallerState;
		if (detLinPred != mAuxiliaryEmptyStackState) {
			
			final Set<LETTER> symbolsReturn = new HashSet<LETTER>();
			for (final STATE state : macrostate.getStates()) {
				symbolsReturn.addAll(mOperand.lettersReturn(state));
			}
			for (final LETTER symbol : symbolsReturn) {
				final Macrostate linPredMacrostate = mDetState2macrostate.get(detLinPred);
				final Macrostate succMacrostate = returnSuccMacrostate(macrostate, linPredMacrostate, symbol);
				if (!succMacrostate.getStates().isEmpty()) {
					STATE succDetState = mMacrostate2detState.get(succMacrostate);
					if (succDetState == null) {
						succDetState = succMacrostate.getContent();
						mResult.addState(false, succMacrostate.mIsFinal, succDetState);
						mMacrostate2detState.put(succMacrostate, succDetState);
						mDetState2macrostate.put(succDetState, succMacrostate);
					}
					mResult.addReturnTransition(detState, detLinPred, symbol, succDetState);
					addSummary(detLinPred, succDetState);
					for (final STATE detLinPredCallerState : getKnownCallerStates(detLinPred)) {
						enqueueAndMark(succDetState, detLinPredCallerState);
					}
				}
				
			}
			
		}
		
	}
	
	/**
	 * Compute successor Macrostate under internal transition of a Macrostate
	 * and symbol.
	 */
	private Macrostate internalSuccMacrostate(final Macrostate macrostate, final LETTER symbol) {
		final Macrostate succMacrostate = new Macrostate();
		for (final STATE state : macrostate.getStates()) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(state, symbol)) {
				final STATE succ = trans.getSucc();
				final Set<STATE> callerStates = macrostate.getCallerStates(state);
				succMacrostate.addPairs(succ, callerStates);
			}
		}
		return succMacrostate;
	}
	
	/**
	 * Compute successor Macrostate under call transition of a Macrostate
	 * and symbol.
	 */
	private Macrostate callSuccMacrostate(final Macrostate macrostate, final LETTER symbol) {
		final Macrostate succMacrostate = new Macrostate();
		for (final STATE state : macrostate.getStates()) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(state, symbol)) {
				final STATE succ = trans.getSucc();
				succMacrostate.addPair(succ, state);
			}
		}
		return succMacrostate;
	}
	
	/**
	 * Compute successor Macrostate under return transition of a Macrostate,
	 * a linear predecessor Macrostate and a symbol.
	 */
	private Macrostate returnSuccMacrostate(final Macrostate macrostate,
			final Macrostate linPredMacrostate, final LETTER symbol) {
		final Macrostate succMacrostate = new Macrostate();
		for (final STATE state : macrostate.getStates()) {
			for (final STATE linPred : macrostate.getCallerStates(state)) {
				for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(state, linPred,
						symbol)) {
					final STATE succ = trans.getSucc();
					final Set<STATE> callerStates =
							linPredMacrostate.getCallerStates(linPred);
					if (callerStates != null) {
						succMacrostate.addPairs(succ, callerStates);
					}
				}
			}
		}
		return succMacrostate;
	}
	
	private class StatePair {
		private final STATE mState;
		private final STATE mCallerState;
		private final int mHashCode;
		
		public StatePair(final STATE state, final STATE callerState) {
			this.mState = state;
			this.mCallerState = callerState;
			mHashCode = computeHashCode();
		}
		
		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			@SuppressWarnings("unchecked")
			final StatePair other = (StatePair) obj;
			if (!getOuterType().equals(other.getOuterType())) {
				return false;
			}
			if (mCallerState == null) {
				if (other.mCallerState != null) {
					return false;
				}
			} else if (!mCallerState.equals(other.mCallerState)) {
				return false;
			}
			if (mState == null) {
				if (other.mState != null) {
					return false;
				}
			} else if (!mState.equals(other.mState)) {
				return false;
			}
			return true;
		}
		
		@Override
		public int hashCode() {
			return mHashCode;
		}
		
		public int computeHashCode() {
			final int prime = 31;
			int hc = 1;
			hc = prime * hc + getOuterType().hashCode();
			hc = prime * hc
					+ ((mCallerState == null) ? 0 : mCallerState.hashCode());
			hc = prime * hc + ((mState == null) ? 0 : mState.hashCode());
			return hc;
		}
		
		@Override
		public String toString() {
			return "CallerState: " + mCallerState + "  State: " + mState;
		}
		
		private DeterminizeSadd getOuterType() {
			return DeterminizeSadd.this;
		}
	}
	
	/**
	 * List of pairs of States.
	 */
	private class Macrostate {
		private final Map<STATE, Set<STATE>> mPairList =
				new HashMap<STATE, Set<STATE>>();
		private boolean mIsFinal = false;
		
		Set<STATE> getStates() {
			return mPairList.keySet();
		}
		
		Set<STATE> getCallerStates(final STATE state) {
			return mPairList.get(state);
		}
		
		boolean isFinal() {
			return mIsFinal;
		}
		
		STATE getContent() {
			return mResult.getStateFactory().determinize(mPairList);
		}
		
		private void addPair(final STATE state, final STATE callerState) {
			if (mOperand.isFinal(state)) {
				mIsFinal = true;
			}
			Set<STATE> callerStates = mPairList.get(state);
			if (callerStates == null) {
				callerStates = new HashSet<STATE>();
				mPairList.put(state, callerStates);
			}
			callerStates.add(callerState);
		}
		
		private void addPairs(final STATE state,
				final Set<STATE> newCallerStates) {
			if (mOperand.isFinal(state)) {
				mIsFinal = true;
			}
			Set<STATE> callerStates = mPairList.get(state);
			if (callerStates == null) {
				callerStates = new HashSet<STATE>();
				mPairList.put(state, callerStates);
			}
			callerStates.addAll(newCallerStates);
		}
		
		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(final Object obj) {
			if (obj instanceof DeterminizeSadd.Macrostate) {
				final Macrostate macrostate = (Macrostate) obj;
				return mPairList.equals(macrostate.mPairList);
			} else {
				return false;
			}
		}
		
		@Override
		public int hashCode() {
			return mPairList.hashCode();
		}
		
		@Override
		public String toString() {
			return mPairList.toString();
		}
	}
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		mLogger.info("Testing correctness of determinization");
		boolean correct = true;
		
		final INestedWordAutomaton<LETTER, STATE> resultDD =
				(new DeterminizeDD<LETTER, STATE>(mServices, stateFactory, mOperand)).getResult();
		correct &= new IsIncluded<>(mServices, stateFactory, resultDD, mResult).getResult();
		correct &= new IsIncluded<>(mServices, stateFactory, mResult, resultDD).getResult();
		mLogger.info("Finished testing correctness of determinization");
		return correct;
	}
}
