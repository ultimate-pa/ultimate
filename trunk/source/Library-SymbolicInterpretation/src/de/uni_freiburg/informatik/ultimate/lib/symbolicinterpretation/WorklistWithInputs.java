package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

public class WorklistWithInputs<K> {

	private final Map<K, SymbolicState> mWorklist = new LinkedHashMap<>();
	private Entry<K, SymbolicState> mRemovedEntry;

	public void add(final K work, final SymbolicState addInput) {
		mWorklist.merge(work, addInput, (oldInput, newInput) -> oldInput.merge(newInput));
	}

	public boolean advance() {
		if (mWorklist.isEmpty()) {
			return false;
		}
		final Iterator<Entry<K, SymbolicState>> iterator = mWorklist.entrySet().iterator();
		mRemovedEntry = iterator.next();
		iterator.remove();
		return true;
	}

	private void ensureAdvanced() {
		if (mRemovedEntry == null) {
			throw new IllegalStateException("Never called advance() on this worklist.");
		}
	}

	public K getWork() {
		ensureAdvanced();
		return mRemovedEntry.getKey();
	}

	public SymbolicState getInput() {
		ensureAdvanced();
		return mRemovedEntry.getValue();
	}

	@Override
	public String toString() {
		return mWorklist.toString();
	}
}