package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.ArrayDeque;
import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
final class WorklistItem<ACTION, VARDECL> {

	private IAbstractState<ACTION, VARDECL> mPreState;
	private ACTION mAction;
	private Deque<ACTION> mScope;
	private Deque<IAbstractStateStorage<ACTION, VARDECL>> mStorages;

	protected WorklistItem(final IAbstractState<ACTION, VARDECL> pre, final ACTION action,
			IAbstractStateStorage<ACTION, VARDECL> globalStorage) {
		assert action != null;
		assert pre != null;
		assert globalStorage != null;

		mPreState = pre;
		mAction = action;
		mStorages = new ArrayDeque<IAbstractStateStorage<ACTION, VARDECL>>();
		mStorages.addFirst(globalStorage);
	}

	protected WorklistItem(final IAbstractState<ACTION, VARDECL> pre, final ACTION action,
			WorklistItem<ACTION, VARDECL> oldItem) {
		assert pre != null;
		assert action != null;
		assert oldItem != null;

		mPreState = pre;
		mAction = action;
		mScope = oldItem.getScopes();
		mStorages = oldItem.getStorages();
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
		if (mScope == null) {
			mScope = new ArrayDeque<ACTION>();
		}
		mScope.addFirst(scope);
		mStorages.addFirst(getCurrentStorage().createStorage());
	}

	public ACTION getCurrentScope() {
		if (mScope == null || mScope.isEmpty()) {
			return null;
		}
		return mScope.peek();
	}

	public ACTION removeCurrentScope() {
		if (mScope == null || mScope.isEmpty()) {
			return null;
		}
		mStorages.removeFirst();
		return mScope.removeFirst();
	}

	private Deque<ACTION> getScopes() {
		if (mScope == null || mScope.isEmpty()) {
			return null;
		}
		return new ArrayDeque<>(mScope);
	}

	public IAbstractStateStorage<ACTION, VARDECL> getCurrentStorage() {
		assert !mStorages.isEmpty();
		return mStorages.peek();
	}

	private Deque<IAbstractStateStorage<ACTION, VARDECL>> getStorages() {
		assert !mStorages.isEmpty();
		return new ArrayDeque<>(mStorages);
	}

}
