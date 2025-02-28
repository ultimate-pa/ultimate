package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness;

import java.util.List;
import java.util.Objects;

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

	@Override
	public int hashCode() {
		return Objects.hash(mIndex, mStates);
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
		final ProductState<?> other = (ProductState<?>) obj;
		return mIndex == other.mIndex && Objects.equals(mStates, other.mStates);
	}

	@Override
	public String toString() {
		return mStates + "; " + mIndex;
	}
}
