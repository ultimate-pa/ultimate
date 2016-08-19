/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * A worklist item is used by {@link FixpointEngine} to store intermediate results from the effect calculation for one
 * transition.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
final class WorklistItem<STATE extends IAbstractState<STATE, ACTION, VARDECL>, ACTION, VARDECL, LOCATION> {

	private final STATE mPreState;
	private final ACTION mAction;
	private final Deque<IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>> mScopedStorages;
	private final Deque<LOCATION> mActiveLoops;
	private final Map<LOCATION, Pair<Integer, STATE>> mLoopPairs;
	private final WorklistItem<STATE, ACTION, VARDECL, LOCATION> mPredecessor;
	private final SummaryMap<STATE, ACTION, VARDECL, LOCATION> mSummaryMap;

	private STATE mHierachicalPreState;
	private Deque<Pair<ACTION, STATE>> mScopes;

	WorklistItem(final STATE pre, final ACTION action,
			final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> globalStorage,
			final SummaryMap<STATE, ACTION, VARDECL, LOCATION> summaryMap) {
		assert action != null;
		assert pre != null : "Prestate may not be null";
		assert globalStorage != null;

		mHierachicalPreState = pre;
		mPreState = pre;
		mAction = action;
		mScopedStorages = new ArrayDeque<IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>>();
		mScopedStorages.addFirst(globalStorage);
		mActiveLoops = new ArrayDeque<>();
		mLoopPairs = new HashMap<>();
		mPredecessor = null;
		mSummaryMap = summaryMap;
	}

	WorklistItem(final STATE pre, final ACTION action, final WorklistItem<STATE, ACTION, VARDECL, LOCATION> oldItem) {
		assert pre != null;
		assert action != null;
		assert oldItem != null;
		mPredecessor = oldItem;
		mPreState = pre;
		mAction = action;
		mSummaryMap = oldItem.mSummaryMap;
		mHierachicalPreState = oldItem.getHierachicalPreState();
		mScopes = oldItem.getScopesCopy();
		mScopedStorages = oldItem.getStoragesCopy();
		mActiveLoops = new ArrayDeque<>(oldItem.mActiveLoops);
		mLoopPairs = new HashMap<>(oldItem.mLoopPairs);

	}

	ACTION getAction() {
		return mAction;
	}

	STATE getPreState() {
		return mPreState;
	}

	STATE getHierachicalPreState() {
		return mHierachicalPreState;
	}

	void addScope(final ACTION scope) {
		assert scope != null;
		if (mScopes == null) {
			mScopes = new ArrayDeque<>();
		}
		mScopes.addFirst(new Pair<>(scope, mHierachicalPreState));
		mHierachicalPreState = mPreState;
		mScopedStorages.addFirst(getCurrentStorage().createStorage());
	}

	ACTION getCurrentScope() {
		if (mScopes == null || mScopes.isEmpty()) {
			return null;
		}
		return mScopes.peek().getFirst();
	}

	ACTION removeCurrentScope() {
		if (mScopes == null || mScopes.isEmpty()) {
			return null;
		}
		mScopedStorages.removeFirst();
		final Pair<ACTION, STATE> rtr = mScopes.removeFirst();
		mHierachicalPreState = rtr.getSecond();
		return rtr.getFirst();
	}

	IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> getCurrentStorage() {
		assert !mScopedStorages.isEmpty();
		return mScopedStorages.peek();
	}

	int getCallStackDepth() {
		if (mScopes == null || mScopes.isEmpty()) {
			return 0;
		}
		return mScopes.size();
	}

	/**
	 *
	 * @return A {@link Deque} that contains pairs of scopes and the corresponding state storage.
	 */
	Deque<Pair<ACTION, IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>>> getStack() {
		final ArrayDeque<Pair<ACTION, IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>>> rtr =
				new ArrayDeque<>();
		final Iterator<IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>> storageIter =
				mScopedStorages.descendingIterator();
		// first, add the global storage
		rtr.add(new Pair<ACTION, IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>>(null, storageIter.next()));
		if (mScopes == null || mScopes.isEmpty()) {
			return rtr;
		}

		final Iterator<Pair<ACTION, STATE>> scopeIter = mScopes.descendingIterator();

		while (scopeIter.hasNext() && storageIter.hasNext()) {
			rtr.add(new Pair<ACTION, IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>>(
					scopeIter.next().getFirst(), storageIter.next()));
		}
		assert !scopeIter.hasNext();
		assert !storageIter.hasNext();

		return rtr;
	}

	boolean isActiveLoopHead(final LOCATION currentLoopHead) {
		return !mActiveLoops.isEmpty() && mActiveLoops.peek() == currentLoopHead;
	}

	int leaveCurrentLoop() {
		assert !mActiveLoops.isEmpty() : "Active loops is empty";
		final LOCATION lastLoopHead = mActiveLoops.pop();
		final Pair<Integer, STATE> loopPair = mLoopPairs.get(lastLoopHead);
		assert loopPair != null;
		return loopPair.getFirst();
	}

	int enterLoop(final LOCATION loopHead, final STATE prestate) {
		if (mActiveLoops.isEmpty() || !mActiveLoops.peek().equals(loopHead)) {
			mActiveLoops.push(loopHead);
		}
		Pair<Integer, STATE> loopPair = mLoopPairs.get(loopHead);
		if (loopPair == null) {
			loopPair = new Pair<Integer, STATE>(0, prestate);
		} else {
			loopPair = new Pair<Integer, STATE>(loopPair.getFirst() + 1, prestate);
		}
		mLoopPairs.put(loopHead, loopPair);
		return loopPair.getFirst();
	}

	Pair<Integer, STATE> getLoopPair(final LOCATION loopHead) {
		return mLoopPairs.get(loopHead);
	}

	WorklistItem<STATE, ACTION, VARDECL, LOCATION> getPredecessor() {
		return mPredecessor;
	}

	void saveSummary(final STATE postState) {
		// called when ACTION is a return; but before the scope is changed
		// meaning that the scope is the corresponding call, and one of its predecessors is the matching summary
		mSummaryMap.addSummary(mHierachicalPreState, postState, getCurrentScope());
	}

	STATE getSummaryPostState(final ACTION summary, final STATE preState) {
		return mSummaryMap.getSummaryPostState(summary, preState);
	}

	private Deque<Pair<ACTION, STATE>> getScopesCopy() {
		if (mScopes == null || mScopes.isEmpty()) {
			return null;
		}
		return new ArrayDeque<>(mScopes);
	}

	private Deque<IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>> getStoragesCopy() {
		assert !mScopedStorages.isEmpty();
		return new ArrayDeque<>(mScopedStorages);
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder().append("[").append(mPreState.hashCode()).append("]--[")
				.append(mAction.hashCode()).append("]--> ? (Scope={[G]");
		final Iterator<Pair<ACTION, STATE>> iter = mScopes.descendingIterator();
		while (iter.hasNext()) {
			builder.append("[").append(iter.next().getFirst().hashCode()).append("]");
		}
		builder.append("})");
		return builder.toString();
	}
}
