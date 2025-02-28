package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class ProductState<STATE> {
	private final List<STATE> mStates;
	private final int mIndex;

	public ProductState(final List<STATE> states, final int index) {
		mStates = states;
		mIndex = index;
	}

	public STATE getState(final int index) {
		return mStates.get(index);
	}

	public int getIndex() {
		return mIndex;
	}

	public ProductState<STATE> extend(final STATE state) {
		return new ProductState<>(DataStructureUtils.concat(mStates, List.of(state)), mIndex);
	}
}
