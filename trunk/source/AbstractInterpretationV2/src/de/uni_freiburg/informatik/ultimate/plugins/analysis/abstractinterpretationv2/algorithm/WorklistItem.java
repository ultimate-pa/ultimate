package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.ArrayDeque;
import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 */
final class WorklistItem<ACTION, VARDECL> {

	private IAbstractState<ACTION, VARDECL> mPreState;
	private ACTION mAction;
	private Deque<ACTION> mScopes;
	private Deque<IAbstractStateStorage<ACTION, VARDECL>> mScopedStorages;

	protected WorklistItem(final IAbstractState<ACTION, VARDECL> pre, final ACTION action,
			IAbstractStateStorage<ACTION, VARDECL> globalStorage) {
		assert action != null;
		assert pre != null;
		assert globalStorage != null;

		mPreState = pre;
		mAction = action;
		mScopedStorages = new ArrayDeque<IAbstractStateStorage<ACTION, VARDECL>>();
		mScopedStorages.addFirst(globalStorage);
	}

	protected WorklistItem(final IAbstractState<ACTION, VARDECL> pre, final ACTION action,
			WorklistItem<ACTION, VARDECL> oldItem) {
		assert pre != null;
		assert action != null;
		assert oldItem != null;

		mPreState = pre;
		mAction = action;
		mScopes = oldItem.getScopes();
		mScopedStorages = oldItem.getStorages();
	}

	public ACTION getAction() {
		return mAction;
	}

	public void setAction(ACTION action) {
		assert action != null;
		mAction = action;
	}

	public IAbstractState<ACTION, VARDECL> getPreState() {
		return mPreState;
	}

	public void setPreState(IAbstractState<ACTION, VARDECL> preState) {
		assert preState != null;
		mPreState = preState;
	}

	public void addScope(ACTION scope) {
		assert scope != null;
		if (mScopes == null) {
			mScopes = new ArrayDeque<ACTION>();
		}
		mScopes.addFirst(scope);
		mScopedStorages.addFirst(getCurrentStorage().createStorage());
	}

	public ACTION getCurrentScope() {
		if (mScopes == null || mScopes.isEmpty()) {
			return null;
		}
		return mScopes.peek();
	}

	public ACTION removeCurrentScope() {
		if (mScopes == null || mScopes.isEmpty()) {
			return null;
		}
		mScopedStorages.removeFirst();
		return mScopes.removeFirst();
	}

	public IAbstractStateStorage<ACTION, VARDECL> getCurrentStorage() {
		assert !mScopedStorages.isEmpty();
		return mScopedStorages.peek();
	}

	public int getCallStackDepth() {
		if (mScopes == null || mScopes.isEmpty()) {
			return 0;
		}
		return mScopes.size();
	}

	private Deque<ACTION> getScopes() {
		if (mScopes == null || mScopes.isEmpty()) {
			return null;
		}
		return new ArrayDeque<>(mScopes);
	}

	private Deque<IAbstractStateStorage<ACTION, VARDECL>> getStorages() {
		assert !mScopedStorages.isEmpty();
		return new ArrayDeque<>(mScopedStorages);
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder().append("[").append(mPreState.hashCode()).append("]--[")
				.append(mAction.hashCode()).append("]--> ? (Scope={");
		for (final ACTION scope : mScopes) {
			builder.append("[").append(scope.hashCode()).append("]");
		}
		builder.append("}");
		return builder.toString();
	}

}
