package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.Objects;

public class StringRankedLetter implements IRankedLetter {

	private final String mString;
	private final int mRank;

	public StringRankedLetter(final String string, final int rank) {
		mString = string;
		mRank = rank;
	}

	@Override
	public int getRank() {
		return mRank;
	}

	@Override
	public String toString() {
		return "#" + mRank + ":" + mString;
		// return mString + " (#" + mRank + ")";
	}

	@Override
	public int hashCode() {
		return Objects.hash(mRank, mString);
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
		final StringRankedLetter other = (StringRankedLetter) obj;
		if (mRank != other.mRank) {
			return false;
		}
		if (mString == null) {
			if (other.mString != null) {
				return false;
			}
		} else if (!mString.equals(other.mString)) {
			return false;
		}
		return true;
	}

}
