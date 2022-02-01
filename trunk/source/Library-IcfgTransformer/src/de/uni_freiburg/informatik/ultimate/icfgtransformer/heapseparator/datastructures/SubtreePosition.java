package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Represents a node/subtree position in a ranked Tree.
 * <p>
 * The position is represented as a sequence of numbers indicating which "turns" to take from the root.
 * <p>
 * (Basically this is a wrapper for a List of Integers.)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class SubtreePosition {

	List<Integer> mPosition;

	/**
	 * The root position
	 */
	public SubtreePosition() {
		mPosition = Collections.emptyList();
	}

	public SubtreePosition(final List<Integer> newPosition) {
		mPosition = Collections.unmodifiableList(newPosition);
	}

	public SubtreePosition append(final int i) {
		final List<Integer> newPosition = new ArrayList<>(depth() + 1);
		newPosition.addAll(mPosition);
		newPosition.add(i);
		return new SubtreePosition(newPosition);
	}

	public int depth() {
		return mPosition.size();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mPosition == null) ? 0 : mPosition.hashCode());
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
		if (getClass() != obj.getClass()) {
			return false;
		}
		final SubtreePosition other = (SubtreePosition) obj;
		if (mPosition == null) {
			if (other.mPosition != null) {
				return false;
			}
		} else if (!mPosition.equals(other.mPosition)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return "SubtreePosition " + mPosition;
	}
}

