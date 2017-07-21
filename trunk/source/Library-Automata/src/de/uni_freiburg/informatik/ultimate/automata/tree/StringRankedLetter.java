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
}
