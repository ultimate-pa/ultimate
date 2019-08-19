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
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractTransformer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * A worklist item is used by {@link FixpointEngine} to store intermediate results from the effect calculation for one
 * transition.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
final class BackwardsWorklistItem<STATE extends IAbstractState<STATE>, ACTION, VARDECL, LOC>
		implements IWorklistItem<STATE, ACTION, LOC> {

	private final DisjunctiveAbstractState<STATE> mState;
	private final ACTION mAction;

	private final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> mPredecessor;
	private final SummaryMap<STATE, ACTION, LOC> mSummaryMap;
	private final Deque<ScopeStackItem> mScopes;

	private ScopeStackItem mCurrentScope;

	/**
	 * Create initial {@link BackwardsWorklistItem}.
	 *
	 * @param pre
	 * @param action
	 * @param globalStorage
	 * @param summaryMap
	 */
	BackwardsWorklistItem(final DisjunctiveAbstractState<STATE> pre, final ACTION action,
			final IAbstractStateStorage<STATE, ACTION, LOC> globalStorage,
			final SummaryMap<STATE, ACTION, LOC> summaryMap) {
		mState = pre;
		mAction = action;
		mPredecessor = null;
		mSummaryMap = summaryMap;
		mCurrentScope = new ScopeStackItem(globalStorage, pre);
		mScopes = new ArrayDeque<>();
		mScopes.add(mCurrentScope);
	}

	/**
	 * Create new {@link BackwardsWorklistItem} from the result of {@link IAbstractTransformer}s apply functions.
	 *
	 * @param pre
	 * @param action
	 * @param oldItem
	 */
	BackwardsWorklistItem(final DisjunctiveAbstractState<STATE> pre, final ACTION action,
			final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> oldItem) {
		mState = pre;
		mAction = action;
		mPredecessor = oldItem;
		mSummaryMap = oldItem.mSummaryMap;
		mScopes = new ArrayDeque<>(oldItem.mScopes);
		mCurrentScope = mScopes.peek();
	}

	@Override
	public ACTION getAction() {
		return mAction;
	}

	@Override
	public DisjunctiveAbstractState<STATE> getState() {
		return mState;
	}

	DisjunctiveAbstractState<STATE> getHierachicalState() {
		return mCurrentScope.getScopeHierState();
	}

	ACTION getCurrentScope() {
		return mCurrentScope.getAction();
	}

	private Map<LOC, Pair<Integer, DisjunctiveAbstractState<STATE>>> getLoopPairs() {
		return mCurrentScope.getLoopPairs();
	}

	/**
	 * Has to be called whenever {@link FixpointEngine} enters a scope.
	 *
	 * @param scope
	 * @param postState
	 */
	void addScope(final ACTION scope, final DisjunctiveAbstractState<STATE> postCallState) {
		assert scope != null;
		final ScopeStackItem newScopeStack =
				new ScopeStackItem(scope, mState, postCallState, getCurrentStorage().createStorage(scope));
		mScopes.addFirst(newScopeStack);
		mCurrentScope = newScopeStack;
	}

	/**
	 * Has to be called whenever {@link FixpointEngine} leaves a scope. Ensures that the state storage is in the correct
	 * state and that the summary map is updated.
	 *
	 * @param preReturnState
	 *            The post state after leaving the current scope.
	 * @return The scope that left.
	 */
	ACTION removeCurrentScope(final DisjunctiveAbstractState<STATE> preReturnState) {
		final ScopeStackItem currentScopeItem = removeCurrentScopeWithoutSummary();
		if (currentScopeItem == null) {
			// happens when we leave the global scope
			return null;
		}
		// called when ACTION is a return; but before the scope is changed
		// meaning that the scope is the corresponding call, and one of its predecessors is the matching summary
		mSummaryMap.addSummary(currentScopeItem.getScopeOldState(), preReturnState, currentScopeItem.getAction());
		return currentScopeItem.getAction();
	}

	DisjunctiveAbstractState<STATE> getSummaryPostState(final ACTION summary,
			final DisjunctiveAbstractState<STATE> preState) {
		return mSummaryMap.getSummaryPostState(summary, preState);
	}

	private ScopeStackItem removeCurrentScopeWithoutSummary() {
		final ScopeStackItem rtr = mScopes.removeFirst();
		if (mScopes.isEmpty()) {
			mCurrentScope = null;
		} else {
			mCurrentScope = mScopes.peekFirst();
		}
		return rtr;
	}

	IAbstractStateStorage<STATE, ACTION, LOC> getCurrentStorage() {
		return mCurrentScope.getStorage();
	}

	int getScopeStackDepth() {
		return mScopes.size();
	}

	/**
	 *
	 * @return A {@link Deque} that contains pairs of scopes and the corresponding state storage.
	 */
	Deque<Pair<ACTION, IAbstractStateStorage<STATE, ACTION, LOC>>> getScopeStack() {
		final Deque<Pair<ACTION, IAbstractStateStorage<STATE, ACTION, LOC>>> rtr = new ArrayDeque<>();
		final Iterator<ScopeStackItem> scopeIter = mScopes.descendingIterator();
		while (scopeIter.hasNext()) {
			final ScopeStackItem current = scopeIter.next();
			rtr.add(new Pair<>(current.getAction(), current.getStorage()));
		}
		return rtr;
	}

	Deque<Pair<ACTION, DisjunctiveAbstractState<STATE>>> getScopeWideningStack() {
		final Deque<Pair<ACTION, DisjunctiveAbstractState<STATE>>> rtr = new ArrayDeque<>();
		final Iterator<ScopeStackItem> scopeIter = mScopes.descendingIterator();
		while (scopeIter.hasNext()) {
			final ScopeStackItem current = scopeIter.next();
			rtr.add(new Pair<>(current.getAction(), current.getScopeOldState()));
		}
		return rtr;
	}

	int enterLoop(final LOC loopHead) {
		final DisjunctiveAbstractState<STATE> prestate = getState();
		final Pair<Integer, DisjunctiveAbstractState<STATE>> loopPair = getLoopPairs().get(loopHead);
		final Pair<Integer, DisjunctiveAbstractState<STATE>> newLoopPair;
		if (loopPair == null) {
			newLoopPair = new Pair<>(0, prestate);
		} else {
			newLoopPair = new Pair<>(loopPair.getFirst() + 1, prestate);
		}
		getLoopPairs().put(loopHead, newLoopPair);
		return newLoopPair.getFirst();
	}

	Pair<Integer, DisjunctiveAbstractState<STATE>> getLoopPair(final LOC loopHead) {
		return getLoopPairs().get(loopHead);
	}

	@Override
	public BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> getPredecessor() {
		return mPredecessor;
	}

	@Override
	public String toString() {
		final String preStateHashCode = mState == null ? "?" : String.valueOf(mState.hashCode());
		final StringBuilder builder = new StringBuilder().append('[').append(preStateHashCode).append("]--[")
				.append(mAction.hashCode()).append("]--> ? (Scope={");
		final Iterator<ScopeStackItem> iter = mScopes.descendingIterator();
		while (iter.hasNext()) {
			final ACTION currentAction = iter.next().getAction();
			if (currentAction != null) {
				builder.append(LoggingHelper.getHashCodeString(currentAction));
			} else {
				builder.append("[G]");
			}
		}
		builder.append("})");
		return builder.toString();
	}

	String toExtendedString() {
		return toString() + " Pre: " + LoggingHelper.getHashCodeString(mState) + " "
				+ Optional.ofNullable(mState).map(a -> a.toLogString()).orElse("?") + " HierPre: "
				+ LoggingHelper.getHashCodeString(getHierachicalState()) + " "
				+ Optional.ofNullable(getHierachicalState()).map(a -> a.toLogString()).orElse("?");
	}

	/**
	 * Container for scope stack items.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	private final class ScopeStackItem {
		private final ACTION mScope;
		private final DisjunctiveAbstractState<STATE> mScopeHierachicalPreState;
		private final DisjunctiveAbstractState<STATE> mScopeFirstState;
		private final IAbstractStateStorage<STATE, ACTION, LOC> mStorage;
		private final Map<LOC, Pair<Integer, DisjunctiveAbstractState<STATE>>> mLoopPairs;

		private ScopeStackItem(final ACTION action, final DisjunctiveAbstractState<STATE> hierPre,
				final DisjunctiveAbstractState<STATE> scopeFirst,
				final IAbstractStateStorage<STATE, ACTION, LOC> storage) {
			mScope = action;
			mScopeHierachicalPreState = hierPre;
			mScopeFirstState = scopeFirst;
			mStorage = storage;
			mLoopPairs = new HashMap<>();
		}

		/**
		 * Create global storage
		 *
		 * @param storage
		 * @param pre
		 */
		private ScopeStackItem(final IAbstractStateStorage<STATE, ACTION, LOC> storage,
				final DisjunctiveAbstractState<STATE> pre) {
			this(null, pre, pre, storage);
		}

		ACTION getAction() {
			return mScope;
		}

		DisjunctiveAbstractState<STATE> getScopeHierState() {
			return mScopeHierachicalPreState;
		}

		DisjunctiveAbstractState<STATE> getScopeOldState() {
			return mScopeFirstState;
		}

		IAbstractStateStorage<STATE, ACTION, LOC> getStorage() {
			return mStorage;
		}

		Map<LOC, Pair<Integer, DisjunctiveAbstractState<STATE>>> getLoopPairs() {
			return mLoopPairs;
		}
	}
}
