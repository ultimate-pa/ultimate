package de.uni_freiburg.informatik.ultimate.util.relation;

/**
 * Generic Triple.
 * 
 * @author Matthias Heizmann
 *
 */
public class Pair<E1, E2> {

	protected E1 mFirstElement;
	protected E2 mSecondElement;

	public Pair(E1 first, E2 second) {
		super();
		mFirstElement = first;
		mSecondElement = second;
	}

	public E1 getFirst() {
		return mFirstElement;
	}

	public E2 getSecond() {
		return mSecondElement;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + mFirstElement.hashCode();
		result = prime * result + mSecondElement.hashCode();
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		Pair<?, ?> other = (Pair<?, ?>) obj;
		if (mFirstElement == null) {
			if (other.mFirstElement != null) {
				return false;
			}
		} else if (!mFirstElement.equals(other.mFirstElement)) {
			return false;
		}
		if (mSecondElement == null) {
			if (other.mSecondElement != null) {
				return false;
			}
		} else if (!mSecondElement.equals(other.mSecondElement)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return "[" + mFirstElement + ", " + mSecondElement + "]";
	}
}
