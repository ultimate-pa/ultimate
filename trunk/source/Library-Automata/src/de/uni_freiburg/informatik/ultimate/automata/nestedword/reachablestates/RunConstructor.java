/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.StateContainer.DownStateProp;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.ITransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;

/**
 * Construction of initial runs and runs for summaries. Runs are constructed
 * backwards, therefore mStart is the last state of the run and mGoal is
 * the first state of the run.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
class RunConstructor<LETTER, STATE> {
	private final AutomataLibraryServices mServices;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mNwars;
	private final StateContainer<LETTER, STATE> mStart;
	/**
	 * If goal is a down state of start we construct a run whose first state
	 * is goal and whose last state is start. If goal is null we construct
	 * an initial run whose last state is start.
	 */
	private final StateContainer<LETTER, STATE> mGoal;
	private final Set<SummaryWithObligation> mForbiddenSummaries;
	private final boolean mFindSummary;
	private final Summary<LETTER, STATE> mSummary;
	private final boolean mSummaryMustContainAccepting;
	private boolean mGoalFound;
	private final Set<StateContainerWithObligation> mVisited = new HashSet<>();
	
	/**
	 * Construction of an initial run whose last state is start.
	 */
	public RunConstructor(final AutomataLibraryServices services,
			final NestedWordAutomatonReachableStates<LETTER, STATE> nwars, final StateContainer<LETTER, STATE> start) {
		mServices = services;
		mNwars = nwars;
		mStart = start;
		mGoal = null;
		mForbiddenSummaries = Collections.emptySet();
		mFindSummary = false;
		mSummary = null;
		mSummaryMustContainAccepting = false;
	}
	
	/**
	 * Construction of run whose last state is start. The state goal can be
	 * either a down state of start or null.
	 * If goal is a down state of start we construct a run whose first state
	 * is goal and whose last state is start. If goal is null we construct
	 * an initial run whose last state is start.
	 */
	public RunConstructor(final AutomataLibraryServices services,
			final NestedWordAutomatonReachableStates<LETTER, STATE> nwars, final Summary<LETTER, STATE> summary,
			final boolean summaryMustContainAccepting) {
		mServices = services;
		mNwars = nwars;
		mStart = summary.getLinPred();
		mGoal = summary.getHierPred();
		mFindSummary = true;
		mSummary = summary;
		mSummaryMustContainAccepting = summaryMustContainAccepting;
		final SummaryWithObligation summaryWithObligation =
				new SummaryWithObligation(mSummary, mSummaryMustContainAccepting);
		mForbiddenSummaries = Collections.singleton(summaryWithObligation);
	}
	
	/**
	 * Run construction for a summary where we may not take any summary in
	 * forbiddenSummaries. This avoids endless loop in recursive calls (if there
	 * is a run that takes a summary twice, then there is a run that takes the
	 * summary once).
	 */
	private RunConstructor(final AutomataLibraryServices services,
			final NestedWordAutomatonReachableStates<LETTER, STATE> nwars, final Summary<LETTER, STATE> summary,
			final boolean summaryMustContainAccepting, final Set<SummaryWithObligation> forbiddenSummaries) {
		mServices = services;
		mNwars = nwars;
		mStart = summary.getLinPred();
		mGoal = summary.getHierPred();
		mFindSummary = true;
		mSummary = summary;
		mSummaryMustContainAccepting = summaryMustContainAccepting;
		final SummaryWithObligation summaryWithObligation =
				new SummaryWithObligation(mSummary, mSummaryMustContainAccepting);
		mForbiddenSummaries = new HashSet<>(forbiddenSummaries);
		mForbiddenSummaries.add(summaryWithObligation);
	}
	
	/**
	 * Find suitable predecessor in run construction. Returns incoming
	 * transition from the state with the lowest serial number (that has
	 * not been visited before).
	 */
	@SuppressWarnings("unchecked")
	private Collection<TransitionWithObligation> findSuitablePredecessors(final StateContainerWithObligation current) {
		final SortedMap<Integer, Object> number2transition = new TreeMap<>();
		Set<RunConstructor<LETTER, STATE>.TransitionWithObligation> resultSingleton =
				findSuitablePredecessorsInternal(current, number2transition);
		if (resultSingleton != null) {
			return resultSingleton;
		}
		resultSingleton = findSuitablePredecessorsCall(current, number2transition);
		if (resultSingleton != null) {
			return resultSingleton;
		}
		resultSingleton = findSuitablePredecessorsReturn(current, number2transition);
		if (resultSingleton != null) {
			return resultSingleton;
		}
		
		final ArrayList<TransitionWithObligation> result = new ArrayList<>();
		for (final Object value : number2transition.values()) {
			if (value instanceof RunConstructor.TransitionWithObligation) {
				final TransitionWithObligation two = (TransitionWithObligation) value;
				assert two.getObject() instanceof IncomingInternalTransition
						|| two.getObject() instanceof IncomingCallTransition;
				result.add(two);
			} else {
				assert value instanceof SortedMap;
				final SortedMap<Integer, TransitionWithObligation> linPredSerial2inTrans =
						(SortedMap<Integer, TransitionWithObligation>) value;
				for (final TransitionWithObligation ret : linPredSerial2inTrans.values()) {
					result.add(ret);
				}
			}
		}
		return result;
	}
	
	@SuppressWarnings("squid:S1168")
	private Set<RunConstructor<LETTER, STATE>.TransitionWithObligation> findSuitablePredecessorsInternal(
			final StateContainerWithObligation current, final SortedMap<Integer, Object> number2transition) {
		for (final IncomingInternalTransition<LETTER, STATE> inTrans : mNwars
				.internalPredecessors(current.getObject().getState())) {
			if (!mFindSummary && mNwars.isInitial(inTrans.getPred())) {
				mGoalFound = true;
				return Collections.singleton(new TransitionWithObligation(inTrans, false));
			}
			final StateContainer<LETTER, STATE> predSc = mNwars.obtainStateContainer(inTrans.getPred());
			if (mFindSummary && !predSc.getDownStates().containsKey(mGoal.getState())) {
				continue;
			}
			final boolean predObligation = current.hasObligation() && !mNwars.isFinal(predSc.getState());
			if (predObligation) {
				assert mFindSummary;
				if (!predSc.hasDownProp(mGoal.getState(), DownStateProp.REACHABLE_FROM_FINAL_WITHOUT_CALL)) {
					continue;
				}
			}
			final StateContainerWithObligation predWithObligation =
					new StateContainerWithObligation(predSc, predObligation);
			if (mVisited.contains(predWithObligation)) {
				continue;
			}
			final int predSerialNumber = predSc.getSerialNumber();
			number2transition.put(predSerialNumber, new TransitionWithObligation(inTrans, predObligation));
		}
		return null;
	}
	
	@SuppressWarnings("squid:S1168")
	private Set<RunConstructor<LETTER, STATE>.TransitionWithObligation> findSuitablePredecessorsCall(
			final StateContainerWithObligation current, final SortedMap<Integer, Object> number2transition) {
		for (final IncomingCallTransition<LETTER, STATE> inTrans : mNwars
				.callPredecessors(current.getObject().getState())) {
			final StateContainer<LETTER, STATE> predSc = mNwars.obtainStateContainer(inTrans.getPred());
			if (mFindSummary) {
				if (mGoal.equals(predSc) && !current.hasObligation()) {
					mGoalFound = true;
					return Collections.singleton(new TransitionWithObligation(inTrans, false));
				}
				continue;
			}
			assert !current.hasObligation();
			if (mNwars.isInitial(inTrans.getPred())) {
				mGoalFound = true;
				return Collections.singleton(new TransitionWithObligation(inTrans, false));
			}
			final StateContainerWithObligation predWithObligation = new StateContainerWithObligation(predSc, false);
			if (mVisited.contains(predWithObligation)) {
				continue;
			}
			final Integer predSerialNumber = predSc.getSerialNumber();
			if (!number2transition.containsKey(predSerialNumber)) {
				number2transition.put(predSerialNumber,
						new TransitionWithObligation(inTrans, false));
			}
		}
		return null;
	}
	
	@SuppressWarnings({ "squid:S1168", "unchecked" })
	private Set<RunConstructor<LETTER, STATE>.TransitionWithObligation> findSuitablePredecessorsReturn(
			final StateContainerWithObligation current, final SortedMap<Integer, Object> number2transition) {
		for (final IncomingReturnTransition<LETTER, STATE> inTrans : mNwars
				.returnPredecessors(current.getObject().getState())) {
			if (!mFindSummary && mNwars.isInitial(inTrans.getHierPred())) {
				mGoalFound = true;
				return Collections.singleton(new TransitionWithObligation(inTrans, false));
			}
			final StateContainer<LETTER, STATE> predSc = mNwars.obtainStateContainer(inTrans.getHierPred());
			if (mFindSummary && !predSc.getDownStates().containsKey(mGoal.getState())) {
				continue;
			}
			final Summary<LETTER, STATE> summary = new Summary<>(mNwars.obtainStateContainer(inTrans.getHierPred()),
					mNwars.obtainStateContainer(inTrans.getLinPred()), inTrans.getLetter(), current.getObject());
			final boolean summaryWillSatisfyObligation = willSummarySatisfyObligation(current, predSc, summary);
			final SummaryWithObligation summaryWithSatifiedObligation = new SummaryWithObligation(summary, false);
			if (summaryWillSatisfyObligation) {
				assert !mForbiddenSummaries.contains(summaryWithSatifiedObligation);
			} else if (mForbiddenSummaries.contains(summaryWithSatifiedObligation)) {
				continue;
			}
			final boolean predObligation =
					current.hasObligation() && !mNwars.isFinal(predSc.getState()) && !summaryWillSatisfyObligation;
			if (predObligation) {
				assert mFindSummary;
				if (!predSc.hasDownProp(mGoal.getState(), DownStateProp.REACHABLE_FROM_FINAL_WITHOUT_CALL)) {
					continue;
				}
			}
			final StateContainerWithObligation predWithObligation =
					new StateContainerWithObligation(predSc, predObligation);
			if (mVisited.contains(predWithObligation)) {
				continue;
			}
			final Integer predSerialNumber = Integer.valueOf(predSc.getSerialNumber());
			final Object previousEntry = number2transition.get(predSerialNumber);
			if (previousEntry instanceof RunConstructor.TransitionWithObligation) {
				// do nothing
				continue;
			}
			assert previousEntry == null || (previousEntry instanceof SortedMap);
			SortedMap<Integer, TransitionWithObligation> linPredSerial2inTrans;
			if (previousEntry == null) {
				linPredSerial2inTrans = new TreeMap<>();
				number2transition.put(predSerialNumber, linPredSerial2inTrans);
			} else {
				linPredSerial2inTrans = (SortedMap<Integer, TransitionWithObligation>) previousEntry;
			}
			final StateContainer<LETTER, STATE> linPredSc = mNwars.obtainStateContainer(inTrans.getLinPred());
			final int linPredSerial = linPredSc.getSerialNumber();
			linPredSerial2inTrans.put(linPredSerial, new TransitionWithObligation(inTrans, predObligation));
		}
		return null;
	}
	
	private boolean willSummarySatisfyObligation(final StateContainerWithObligation current,
			final StateContainer<LETTER, STATE> predSc, final Summary<LETTER, STATE> summary) {
		final boolean summaryWillSatisfyObligation;
		final boolean doWeWantToTakeAcceptingSummary =
				current.hasObligation() && !mNwars.isFinal(predSc.getState()) && mNwars.isAccepting(summary);
		if (doWeWantToTakeAcceptingSummary) {
			final SummaryWithObligation swo = new SummaryWithObligation(summary, true);
			final boolean areWeAllowedToTakeAcceptingSummary = !mForbiddenSummaries.contains(swo);
			if (areWeAllowedToTakeAcceptingSummary) {
				summaryWillSatisfyObligation = true;
			} else {
				summaryWillSatisfyObligation = false;
			}
		} else {
			summaryWillSatisfyObligation = false;
		}
		return summaryWillSatisfyObligation;
	}
	
	/**
	 * Returns run whose first state is mGoal and whose last state is
	 * mStart.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	NestedRun<LETTER, STATE> constructRun() throws AutomataOperationCanceledException {
		//TODO: Check if this timeout check is responsible for problems.
		if (mServices.getProgressAwareTimer() != null
				&& !mServices.getProgressAwareTimer().continueProcessing()) {
			throw new AutomataOperationCanceledException(this.getClass());
		}
		assert !mSummaryMustContainAccepting || mGoal != null;
		if (!mFindSummary && mNwars.isInitial(mStart.getState())) {
			return new NestedRun<>(mStart.getState());
		}
		final boolean startStateHasObligation = mSummaryMustContainAccepting && !mNwars.isFinal(mStart.getState());
		final StateContainerWithObligation startStateWithStartObligation =
				new StateContainerWithObligation(mStart, startStateHasObligation);
		final StateContainerWithObligation current = startStateWithStartObligation;
		final Deque<Iterator<TransitionWithObligation>> predStack = new ArrayDeque<>();
		final Deque<RunWithObligation> takenStack = new ArrayDeque<>();
		return constructRunLoop(startStateWithStartObligation, current, predStack, takenStack);
	}
	
	private NestedRun<LETTER, STATE> constructRunLoop(final StateContainerWithObligation startStateWithStartObligation,
			final StateContainerWithObligation currentIn, final Deque<Iterator<TransitionWithObligation>> predStack,
			final Deque<RunWithObligation> takenStack) throws AutomataOperationCanceledException, AssertionError {
		StateContainerWithObligation current = currentIn;
		// if this is set the last round
		boolean backtrack = false;
		while (true) {
			if (backtrack) {
				backtrack = false;
			} else {
				assert !mVisited.contains(current);
				mVisited.add(current);
				assert predStack.size() == takenStack.size();
				final Collection<TransitionWithObligation> predecessors = findSuitablePredecessors(current);
				predStack.push(predecessors.iterator());
			}
			while (!predStack.peek().hasNext()) {
				predStack.pop();
				if (takenStack.isEmpty()) {
					// I am not able to find a run. Maybe taking this summary was a bad decision.
					assert mGoal != null;
					return null;
				}
				final RunWithObligation wrongDescision = takenStack.pop();
				final StateContainerWithObligation sc = wrongDescision.getStateWithObligation();
				assert mVisited.contains(sc);
				mVisited.remove(sc);
				if (takenStack.isEmpty()) {
					current = startStateWithStartObligation;
				} else {
					final RunWithObligation currentPrefix = takenStack.peek();
					current = currentPrefix.getStateWithObligation();
				}
			}
			
			final TransitionWithObligation transitionWoToLowest = predStack.peek().next();
			assert transitionWoToLowest != null;
			final ITransitionlet<LETTER, STATE> transitionToLowest = transitionWoToLowest.getObject();
			StateContainer<LETTER, STATE> predSc;
			NestedRun<LETTER, STATE> newPrefix;
			if (transitionToLowest instanceof IncomingInternalTransition) {
				final IncomingInternalTransition<LETTER, STATE> inTrans =
						(IncomingInternalTransition<LETTER, STATE>) transitionToLowest;
				predSc = mNwars.obtainStateContainer(inTrans.getPred());
				newPrefix = new NestedRun<>(inTrans.getPred(), inTrans.getLetter(), NestedWord.INTERNAL_POSITION,
						current.getObject().getState());
			} else if (transitionToLowest instanceof IncomingCallTransition) {
				final IncomingCallTransition<LETTER, STATE> inTrans =
						(IncomingCallTransition<LETTER, STATE>) transitionToLowest;
				predSc = mNwars.obtainStateContainer(inTrans.getPred());
				newPrefix = new NestedRun<>(inTrans.getPred(), inTrans.getLetter(), NestedWord.PLUS_INFINITY,
						current.getObject().getState());
			} else if (transitionToLowest instanceof IncomingReturnTransition) {
				final IncomingReturnTransition<LETTER, STATE> inTrans =
						(IncomingReturnTransition<LETTER, STATE>) transitionToLowest;
				predSc = mNwars.obtainStateContainer(inTrans.getHierPred());
				final Summary<LETTER, STATE> summary = new Summary<>(predSc,
						mNwars.obtainStateContainer(inTrans.getLinPred()), inTrans.getLetter(), current.getObject());
				final boolean isAcceptingSummaryRequired = current.hasObligation()
						&& !transitionWoToLowest.hasObligation() && !mNwars.isFinal(predSc.getState());
				assert !isAcceptingSummaryRequired || mNwars.isAccepting(summary);
				final RunConstructor<LETTER, STATE> runConstuctor = new RunConstructor<>(mServices, mNwars, summary,
						isAcceptingSummaryRequired, mForbiddenSummaries);
				newPrefix = runConstuctor.constructRun();
				if (newPrefix == null) {
					// no summary found (because of forbidden summaries?)
					// we have to backtrack
					backtrack = true;
					continue;
				}
			} else {
				throw new AssertionError();
			}
			assert isLastStateInRun(current.getObject(), newPrefix);
			final StateContainerWithObligation predWo =
					new StateContainerWithObligation(predSc, transitionWoToLowest.hasObligation());
			final RunWithObligation newPrefixWo =
					new RunWithObligation(predWo.getObject(), predWo.hasObligation(), newPrefix);
			takenStack.push(newPrefixWo);
			if (mGoalFound) {
				return constructResult(takenStack);
			}
			current = predWo;
		}
	}
	
	private NestedRun<LETTER, STATE> constructResult(final Deque<RunWithObligation> stack) {
		final Iterator<RunWithObligation> it = stack.descendingIterator();
		NestedRun<LETTER, STATE> result = it.next().getNestedRun();
		while (it.hasNext()) {
			result = it.next().getNestedRun().concatenate(result);
		}
		assert isLastStateInRun(mStart, result);
		if (mFindSummary) {
			final NestedRun<LETTER, STATE> returnSuffix = new NestedRun<>(mSummary.getLinPred().getState(),
					mSummary.getLetter(), NestedWord.MINUS_INFINITY, mSummary.getSucc().getState());
			result = result.concatenate(returnSuffix);
		}
		return result;
	}
	
	@SuppressWarnings("squid:S1698")
	private boolean isLastStateInRun(final StateContainer<LETTER, STATE> stateContainer,
			final NestedRun<LETTER, STATE> run) {
		// equality intended here
		return stateContainer.getState() == run.getStateAtPosition(run.getLength() - 1);
	}
	
	/**
	 * Wrapper for object together with a flag.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 * @param <E>
	 *            object type
	 */
	private static class ObjectWithObligation<E> {
		private final E mObject;
		private final boolean mFlag;
		
		public ObjectWithObligation(final E object, final boolean flag) {
			mObject = object;
			mFlag = flag;
		}
		
		public E getObject() {
			return mObject;
		}
		
		/**
		 * @return The value of the flag.
		 */
		public boolean hasObligation() {
			return mFlag;
		}
		
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = prime + (mFlag ? 1231 : 1237);
			result = prime * result + ((mObject == null) ? 0 : mObject.hashCode());
			return result;
		}
		
		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (this.getClass() != obj.getClass()) {
				return false;
			}
			@SuppressWarnings("unchecked")
			final ObjectWithObligation<E> other = (ObjectWithObligation<E>) obj;
			if (mFlag != other.mFlag) {
				return false;
			}
			if (mObject == null) {
				if (other.mObject != null) {
					return false;
				}
			} else if (!mObject.equals(other.mObject)) {
				return false;
			}
			return true;
		}
		
		@Override
		public String toString() {
			return "ObjectWithObligation [mObject=" + mObject + ", mFlag=" + mFlag + "]";
		}
	}
	
	/**
	 * Wrapper for {@link ITransitionlet} together with a flag.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class TransitionWithObligation extends ObjectWithObligation<ITransitionlet<LETTER, STATE>> {
		public TransitionWithObligation(final ITransitionlet<LETTER, STATE> object, final boolean flag) {
			super(object, flag);
		}
	}
	
	/**
	 * Wrapper for {@link StateContainer} together with a flag.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class StateContainerWithObligation extends ObjectWithObligation<StateContainer<LETTER, STATE>> {
		public StateContainerWithObligation(final StateContainer<LETTER, STATE> object, final boolean flag) {
			super(object, flag);
		}
	}
	
	/**
	 * Wrapper for an object together with a flag and a {@link NestedRun}.
	 * <p>
	 * TODO Christian 2016-09-13: The {@link #equals(Object)} method should probably be overwritten.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class RunWithObligation extends StateContainerWithObligation {
		private final NestedRun<LETTER, STATE> mNestedRun;
		
		public RunWithObligation(final StateContainer<LETTER, STATE> object, final boolean flag,
				final NestedRun<LETTER, STATE> nestedRun) {
			super(object, flag);
			mNestedRun = nestedRun;
		}
		
		public NestedRun<LETTER, STATE> getNestedRun() {
			return mNestedRun;
		}
		
		public StateContainerWithObligation getStateWithObligation() {
			return new StateContainerWithObligation(getObject(), hasObligation());
		}
	}
	
	/**
	 * Wrapper for {@link Summary} together with a flag.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class SummaryWithObligation extends ObjectWithObligation<Summary<LETTER, STATE>> {
		public SummaryWithObligation(final Summary<LETTER, STATE> object, final boolean flag) {
			super(object, flag);
		}
	}
}
