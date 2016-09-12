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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsIncluded;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Given two nondeterministic NWAs nwa_minuend and nwa_subtrahend a
 * DifferenceAutomatonBuilder can compute a NWA nwa_difference
 * such that nwa_difference accepts all words that are accepted by nwa_minuend
 * but not by Psi(nwa_subtrahend), i.e.
 * L(nwa_difference) = L(nwa_minuend) \ L( Psi(nwa_subtrahend) ),
 * where Psi is a transformation of the automaton nwa_subtrahend that is defined
 * by an implementation of IStateDeterminizer.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @param <LETTER>
 *            Symbol. Type of the elements of the alphabet over which the
 *            automata are defined.
 * @param <STATE>
 *            Content. Type of the labels that are assigned to the states of
 *            automata. In many cases you want to use String as STATE and your states are
 *            labeled e.g. with "q0", "q1", ...
 */
//TODO: Optimization for special case where subtrahend is closed under
// concatenation with Sigma^*. Use only one DeterminizedState detFin state that
// represents all final states. Each successor of detFin is detFin itself.
public class DifferenceDD<LETTER, STATE> extends DoubleDeckerBuilder<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
	/**
	 * If set the language of the subtrahend is closed under concatenation with
	 * sigma star. This means for determinized subtrahends: Once in the final
	 * state you can never escape the final states. Hence the result can omit
	 * all states where the subtrahend is final.
	 */
	private final boolean mSubtrahendSigmaStarClosed;
	
	private final INestedWordAutomatonSimple<LETTER, STATE> mMinuend;
	private final INestedWordAutomatonSimple<LETTER, STATE> mSubtrahend;
	
	private final IStateDeterminizer<LETTER, STATE> mStateDeterminizer;
	
	/**
	 * Maps a DifferenceState to its representative in the resulting automaton.
	 */
	private final Map<DifferenceState<LETTER, STATE>, STATE> mDiff2res =
			new HashMap<DifferenceState<LETTER, STATE>, STATE>();
			
	/**
	 * Maps a state in resulting automaton to the DifferenceState for which it
	 * was created.
	 */
	private final Map<STATE, DifferenceState<LETTER, STATE>> mRes2diff =
			new HashMap<STATE, DifferenceState<LETTER, STATE>>();
			
	private final IStateFactory<STATE> mStateFactoryForIntersection;
	
//	private INestedWordAutomaton<LETTER,DeterminizedState<LETTER,STATE>> mDeterminizedSubtrahend;
	
	private int mInternalSuccs = 0;
	private int mInternalSuccsCache = 0;
	private int mCallSuccs = 0;
	private int mCallSuccsCache = 0;
	private int mReturnSuccs = 0;
	private int mReturnSuccsCache = 0;
	private int mUnnecessary = 0;
	
	private final Map<DeterminizedState<LETTER, STATE>, DeterminizedState<LETTER, STATE>> mDetStateCache =
			new HashMap<>();
			
	private final Map<DeterminizedState<LETTER, STATE>, Map<LETTER, DeterminizedState<LETTER, STATE>>>
		mInternalSuccessorCache = new HashMap<>();
			
	private final Map<DeterminizedState<LETTER, STATE>, Map<LETTER, DeterminizedState<LETTER, STATE>>>
		mCallSuccessorCache = new HashMap<>();
			
	private final Map<DeterminizedState<LETTER, STATE>, Map<DeterminizedState<LETTER, STATE>,
		Map<LETTER, DeterminizedState<LETTER, STATE>>>> mReturnSuccessorCache = new HashMap<>();
			
	public DifferenceDD(
			final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER, STATE> minuend,
			final INestedWordAutomatonSimple<LETTER, STATE> subtrahend,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer,
			final IStateFactory<STATE> stateFactoryForIntersection,
			final boolean removeDeadEnds,
			final boolean subtrahendSigmaStarClosed) throws AutomataLibraryException {
		super(services);
		this.mSubtrahendSigmaStarClosed = subtrahendSigmaStarClosed;
		mStateFactoryForIntersection = stateFactoryForIntersection;
		this.mMinuend = minuend;
		this.mSubtrahend = subtrahend;
		if (!INestedWordAutomatonSimple.sameAlphabet(this.mMinuend, this.mSubtrahend)) {
			throw new AutomataLibraryException(this.getClass(),
					"Unable to apply operation to automata with different alphabets.");
		}
		mLogger.info(startMessage());
		this.mStateDeterminizer = stateDeterminizer;
		super.mTraversedNwa = new DoubleDeckerAutomaton<LETTER, STATE>(
				mServices,
				minuend.getInternalAlphabet(),
				minuend.getCallAlphabet(),
				minuend.getReturnAlphabet(),
				mStateFactoryForIntersection);
		super.mRemoveDeadEnds = removeDeadEnds;
		
//		mDeterminizedSubtrahend =
//			new NestedWordAutomaton<LETTER,DeterminizedState<LETTER,STATE>>(
//					minuend.getInternalAlphabet(),
//					minuend.getCallAlphabet(),
//					minuend.getReturnAlphabet(),
//					null);
		traverseDoubleDeckerGraph();
		((DoubleDeckerAutomaton<LETTER, STATE>) super.mTraversedNwa).setUp2Down(getUp2DownMapping());
		mLogger.info(exitMessage());
		mLogger.info("Computed internal successors:" + mInternalSuccs);
		mLogger.info("Internal successors via cache:" + mInternalSuccsCache);
		mLogger.info("Computed call successors:" + mCallSuccs);
		mLogger.info("Call successors via cache:" + mCallSuccsCache);
		mLogger.info("Computed return successors:" + mReturnSuccs);
		mLogger.info("Return successors via cache:" + mReturnSuccsCache);
		mLogger.info(mUnnecessary + " times subtrahend state of successor "
				+ "was accepting (use sigma star concat closure?)");
	}
	
	/**
	 * @param stateFactory
	 *            {@link IStateFactory} that is used for intersection
	 *            and determinization
	 */
	public DifferenceDD(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER, STATE> minuend,
			final INestedWordAutomatonSimple<LETTER, STATE> subtrahend) throws AutomataLibraryException {
		super(services);
		this.mSubtrahendSigmaStarClosed = false;
		mStateFactoryForIntersection = stateFactory;
		this.mMinuend = minuend;
		this.mSubtrahend = subtrahend;
		if (!INestedWordAutomatonSimple.sameAlphabet(this.mMinuend, this.mSubtrahend)) {
			throw new AutomataLibraryException(this.getClass(),
					"Unable to apply operation to automata with different alphabets.");
		}
		mLogger.info(startMessage());
		this.mStateDeterminizer =
				new PowersetDeterminizer<LETTER, STATE>(subtrahend, true, stateFactory);
		super.mTraversedNwa = new DoubleDeckerAutomaton<LETTER, STATE>(
				mServices,
				minuend.getInternalAlphabet(),
				minuend.getCallAlphabet(),
				minuend.getReturnAlphabet(),
				mStateFactoryForIntersection);
		super.mRemoveDeadEnds = false;
		
		final Set<LETTER> newInternals = new HashSet<LETTER>();
		newInternals.addAll(minuend.getInternalAlphabet());
		newInternals.retainAll(subtrahend.getInternalAlphabet());
		final Set<LETTER> newCalls = new HashSet<LETTER>();
		newCalls.addAll(minuend.getCallAlphabet());
		newCalls.retainAll(subtrahend.getCallAlphabet());
		final Set<LETTER> newReturns = new HashSet<LETTER>();
		newReturns.addAll(minuend.getReturnAlphabet());
		newReturns.retainAll(subtrahend.getReturnAlphabet());
		
//		mDeterminizedSubtrahend =
//			new NestedWordAutomaton<LETTER,DeterminizedState<LETTER,STATE>>(
//					minuend.getInternalAlphabet(),
//					minuend.getCallAlphabet(),
//					minuend.getReturnAlphabet(),
//					null);
		traverseDoubleDeckerGraph();
		((DoubleDeckerAutomaton<LETTER, STATE>) super.mTraversedNwa).setUp2Down(getUp2DownMapping());
		mLogger.info(exitMessage());
	}
	
	@Override
	public String operationName() {
		return "difference";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Minuend "
				+ mMinuend.sizeInformation() + ". Subtrahend "
				+ mSubtrahend.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result "
				+ mTraversedNwa.sizeInformation() + ". Max degree of Nondeterminism is "
				+ mStateDeterminizer.getMaxDegreeOfNondeterminism()
				+ ". DeterminizedStates: " + mDetStateCache.size();
	}
	
	private DeterminizedState<LETTER, STATE> internalSuccessorCache(
			final DeterminizedState<LETTER, STATE> state,
			final LETTER symbol) {
		final Map<LETTER, DeterminizedState<LETTER, STATE>> symbol2succ =
				mInternalSuccessorCache.get(state);
		if (symbol2succ == null) {
			return null;
		}
		return symbol2succ.get(symbol);
	}
	
	private void putInternalSuccessorCache(
			final DeterminizedState<LETTER, STATE> state,
			final LETTER symbol,
			final DeterminizedState<LETTER, STATE> succ) {
		Map<LETTER, DeterminizedState<LETTER, STATE>> symbol2succ =
				mInternalSuccessorCache.get(state);
		if (symbol2succ == null) {
			symbol2succ = new HashMap<LETTER, DeterminizedState<LETTER, STATE>>();
			mInternalSuccessorCache.put(state, symbol2succ);
		}
		symbol2succ.put(symbol, succ);
	}
	
	private DeterminizedState<LETTER, STATE> callSuccessorCache(
			final DeterminizedState<LETTER, STATE> state,
			final LETTER symbol) {
		final Map<LETTER, DeterminizedState<LETTER, STATE>> symbol2succ =
				mCallSuccessorCache.get(state);
		if (symbol2succ == null) {
			return null;
		}
		return symbol2succ.get(symbol);
	}
	
	private void putCallSuccessorCache(
			final DeterminizedState<LETTER, STATE> state,
			final LETTER symbol,
			final DeterminizedState<LETTER, STATE> succ) {
		Map<LETTER, DeterminizedState<LETTER, STATE>> symbol2succ =
				mCallSuccessorCache.get(state);
		if (symbol2succ == null) {
			symbol2succ = new HashMap<LETTER, DeterminizedState<LETTER, STATE>>();
			mCallSuccessorCache.put(state, symbol2succ);
		}
		symbol2succ.put(symbol, succ);
	}
	
	private DeterminizedState<LETTER, STATE> returnSuccessorCache(
			final DeterminizedState<LETTER, STATE> state,
			final DeterminizedState<LETTER, STATE> linPred,
			final LETTER symbol) {
		final Map<DeterminizedState<LETTER, STATE>, Map<LETTER, DeterminizedState<LETTER, STATE>>> linPred2symbol2succ =
				mReturnSuccessorCache.get(linPred);
		if (linPred2symbol2succ == null) {
			return null;
		}
		final Map<LETTER, DeterminizedState<LETTER, STATE>> symbol2succ =
				linPred2symbol2succ.get(state);
		if (symbol2succ == null) {
			return null;
		}
		return symbol2succ.get(symbol);
	}
	
	private void putReturnSuccessorCache(
			final DeterminizedState<LETTER, STATE> state,
			final DeterminizedState<LETTER, STATE> linPred,
			final LETTER symbol,
			final DeterminizedState<LETTER, STATE> succ) {
		Map<DeterminizedState<LETTER, STATE>, Map<LETTER, DeterminizedState<LETTER, STATE>>> linPred2symbol2succ =
				mReturnSuccessorCache.get(linPred);
		if (linPred2symbol2succ == null) {
			linPred2symbol2succ =
					new HashMap<DeterminizedState<LETTER, STATE>, Map<LETTER, DeterminizedState<LETTER, STATE>>>();
			mReturnSuccessorCache.put(linPred, linPred2symbol2succ);
		}
		Map<LETTER, DeterminizedState<LETTER, STATE>> symbol2succ =
				linPred2symbol2succ.get(state);
		if (symbol2succ == null) {
			symbol2succ = new HashMap<LETTER, DeterminizedState<LETTER, STATE>>();
			linPred2symbol2succ.put(state, symbol2succ);
		}
		symbol2succ.put(symbol, succ);
	}
	
	@Override
	protected Collection<STATE> getInitialStates() {
//		final ArrayList<STATE> resInitials = new ArrayList<>(subtrahend.getInitialStates().size());
		final ArrayList<STATE> resInitials = new ArrayList<>();
		final DeterminizedState<LETTER, STATE> detState = mStateDeterminizer.initialState();
		mDetStateCache.put(detState, detState);
		for (final STATE minuState : mMinuend.getInitialStates()) {
			final boolean isFinal = mMinuend.isFinal(minuState)
					&& !detState.containsFinal();
			final DifferenceState<LETTER, STATE> diffState =
					new DifferenceState<LETTER, STATE>(minuState, detState, isFinal);
			final STATE resState = mStateFactoryForIntersection.intersection(
					diffState.getMinuendState(),
					mStateDeterminizer.getState(diffState.getSubtrahendDeterminizedState()));
			((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addState(true, diffState.isFinal(), resState);
			mDiff2res.put(diffState, resState);
			mRes2diff.put(resState, diffState);
			resInitials.add(resState);
		}
		return resInitials;
	}
	
	@Override
	protected Collection<STATE> buildInternalSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
		final List<STATE> resInternalSuccessors = new LinkedList<STATE>();
		final STATE resState = doubleDecker.getUp();
		final DifferenceState<LETTER, STATE> diffState = mRes2diff.get(resState);
		final STATE minuState =
				diffState.getMinuendState();
		final DeterminizedState<LETTER, STATE> detState =
				diffState.getSubtrahendDeterminizedState();
				
		for (final LETTER symbol : mMinuend.lettersInternal(minuState)) {
			if (!mSubtrahend.getInternalAlphabet().contains(symbol)) {
				continue;
			}
			DeterminizedState<LETTER, STATE> detSucc =
					internalSuccessorCache(detState, symbol);
			if (detState.containsFinal()) {
				mUnnecessary++;
			}
			if (detSucc == null) {
				mInternalSuccs++;
				detSucc = mStateDeterminizer.internalSuccessor(detState, symbol);
				if (mDetStateCache.containsKey(detSucc)) {
					detSucc = mDetStateCache.get(detSucc);
				} else {
					mDetStateCache.put(detSucc, detSucc);
				}
				putInternalSuccessorCache(detState, symbol, detSucc);
			} else {
				mInternalSuccsCache++;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mMinuend.internalSuccessors(minuState,
					symbol)) {
				final STATE minuSucc = trans.getSucc();
				final boolean isFinal = mMinuend.isFinal(minuSucc)
						&& !detSucc.containsFinal();
				final DifferenceState<LETTER, STATE> diffSucc =
						new DifferenceState<LETTER, STATE>(minuSucc, detSucc, isFinal);
				final STATE resSucc = getResState(diffSucc);
				((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addInternalTransition(resState, symbol, resSucc);
				resInternalSuccessors.add(resSucc);
			}
		}
		return resInternalSuccessors;
	}
	
	@Override
	protected Collection<STATE> buildCallSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
		final List<STATE> resCallSuccessors = new LinkedList<STATE>();
		final STATE resState = doubleDecker.getUp();
		final DifferenceState<LETTER, STATE> diffState = mRes2diff.get(resState);
		final STATE minuState =
				diffState.getMinuendState();
		final DeterminizedState<LETTER, STATE> detState =
				diffState.getSubtrahendDeterminizedState();
				
		for (final LETTER symbol : mMinuend.lettersCall(minuState)) {
			if (!mSubtrahend.getCallAlphabet().contains(symbol)) {
				continue;
			}
			DeterminizedState<LETTER, STATE> detSucc =
					callSuccessorCache(detState, symbol);
			if (detState.containsFinal()) {
				mUnnecessary++;
			}
			if (detSucc == null) {
				mCallSuccs++;
				detSucc = mStateDeterminizer.callSuccessor(detState, symbol);
				if (mDetStateCache.containsKey(detSucc)) {
					detSucc = mDetStateCache.get(detSucc);
				} else {
					mDetStateCache.put(detSucc, detSucc);
				}
				putCallSuccessorCache(detState, symbol, detSucc);
			} else {
				mCallSuccsCache++;
			}
			for (final OutgoingCallTransition<LETTER, STATE> trans : mMinuend.callSuccessors(minuState, symbol)) {
				final STATE minuSucc = trans.getSucc();
				if (mSubtrahendSigmaStarClosed && detSucc.containsFinal()) {
					continue;
				}
				final boolean isFinal = mMinuend.isFinal(minuSucc)
						&& !detSucc.containsFinal();
				final DifferenceState<LETTER, STATE> diffSucc =
						new DifferenceState<LETTER, STATE>(minuSucc, detSucc, isFinal);
				final STATE resSucc = getResState(diffSucc);
				((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addCallTransition(resState, symbol, resSucc);
				resCallSuccessors.add(resSucc);
			}
		}
		return resCallSuccessors;
	}
	
	@Override
	protected Collection<STATE> buildReturnSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
		final List<STATE> resReturnSuccessors = new LinkedList<STATE>();
		final STATE resLinPred = doubleDecker.getDown();
		if (resLinPred == mTraversedNwa.getEmptyStackState()) {
			return resReturnSuccessors;
		}
		
		final STATE resState = doubleDecker.getUp();
		final DifferenceState<LETTER, STATE> diffState = mRes2diff.get(resState);
		final STATE minuState =
				diffState.getMinuendState();
		final DeterminizedState<LETTER, STATE> detState =
				diffState.getSubtrahendDeterminizedState();
				
		final DifferenceState<LETTER, STATE> diffLinPred = mRes2diff.get(resLinPred);
		final STATE minuLinPred = diffLinPred.getMinuendState();
		
		final DeterminizedState<LETTER, STATE> detLinPred =
				diffLinPred.getSubtrahendDeterminizedState();
				
		for (final LETTER symbol : mMinuend.lettersReturn(minuState)) {
			
			final Iterable<OutgoingReturnTransition<LETTER, STATE>> minuTransitions =
					mMinuend.returnSuccessors(minuState, minuLinPred, symbol);
					
			// do nothing if there will be no successor difference state
			if (!minuTransitions.iterator().hasNext()) {
				continue;
			}
			
			if (!mSubtrahend.getReturnAlphabet().contains(symbol)) {
				continue;
			}
			
			DeterminizedState<LETTER, STATE> detSucc =
					returnSuccessorCache(detState, detLinPred, symbol);
			if (detState.containsFinal()) {
				mUnnecessary++;
			}
			if (detSucc == null) {
				mReturnSuccs++;
				detSucc = mStateDeterminizer.returnSuccessor(
						detState, detLinPred, symbol);
//				mLogger.debug("Successor of state " + detState + " symbol " +
//						symbol + " linPred " + detLinPred + " is " + detSucc);
				
				if (mDetStateCache.containsKey(detSucc)) {
					detSucc = mDetStateCache.get(detSucc);
				} else {
					mDetStateCache.put(detSucc, detSucc);
				}
				putReturnSuccessorCache(detState, detLinPred, symbol, detSucc);
			} else {
				mReturnSuccsCache++;
			}
			
			for (final OutgoingReturnTransition<LETTER, STATE> trans : minuTransitions) {
				final STATE minuSucc = trans.getSucc();
				final boolean isFinal = mMinuend.isFinal(minuSucc)
						&& !detSucc.containsFinal();
				final DifferenceState<LETTER, STATE> diffSucc =
						new DifferenceState<LETTER, STATE>(minuSucc, detSucc, isFinal);
				final STATE resSucc = getResState(diffSucc);
				((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addReturnTransition(
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
	STATE getResState(final DifferenceState<LETTER, STATE> diffState) {
		if (mDiff2res.containsKey(diffState)) {
			return mDiff2res.get(diffState);
		} else {
			final STATE resState = mStateFactoryForIntersection.intersection(
					diffState.getMinuendState(),
					mStateDeterminizer.getState(diffState.getSubtrahendDeterminizedState()));
			((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addState(false, diffState.isFinal(), resState);
			mDiff2res.put(diffState, resState);
			mRes2diff.put(resState, diffState);
			return resState;
		}
	}
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		boolean correct = true;
		if (mStateDeterminizer instanceof PowersetDeterminizer) {
			mLogger.info("Start testing correctness of " + operationName());
			
			final INestedWordAutomaton<LETTER, STATE> resultSadd =
					(new DifferenceSadd<LETTER, STATE>(mServices, stateFactory, mMinuend, mSubtrahend)).getResult();
			correct &= new IsIncluded<>(mServices, stateFactory, resultSadd, mTraversedNwa).getResult();
			correct &= new IsIncluded<>(mServices, stateFactory, mTraversedNwa, resultSadd).getResult();
			if (!correct) {
				AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices,
						operationName() + "Failed", "language is different",
						mMinuend, mSubtrahend);
			}
			mLogger.info("Finished testing correctness of " + operationName());
		} else {
			mLogger.warn("Unable to test correctness if state determinzier is not the PowersetDeterminizer.");
		}
		return correct;
	}
	
}
