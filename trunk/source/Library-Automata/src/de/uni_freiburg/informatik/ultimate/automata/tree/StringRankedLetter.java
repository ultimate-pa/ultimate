package de.uni_freiburg.informatik.ultimate.automata.tree;

public class StringRankedLetter implements IRankedLetter {
	
	private final String mString;
	private final int mRank;

	public StringRankedLetter(String string, int rank) {
		mString = string;
		mRank = rank;
	}

	@Override
	public int getRank() {
		return mRank;
	}

	@Override
	public String toString() {
		return mString + " (#" + mRank + ")";
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + mRank;
		result = prime * result + ((mString == null) ? 0 : mString.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		StringRankedLetter other = (StringRankedLetter) obj;
		if (mRank != other.mRank)
			return false;
		if (mString == null) {
			if (other.mString != null)
				return false;
		} else if (!mString.equals(other.mString))
			return false;
		return true;
	}
	
	
}
