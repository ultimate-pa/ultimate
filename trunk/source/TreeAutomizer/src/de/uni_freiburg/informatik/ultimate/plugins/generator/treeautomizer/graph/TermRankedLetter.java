package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class TermRankedLetter implements IRankedLetter {
	
	
	private final Term mTerm;
	private final int mRank;

	public TermRankedLetter(Term term, int rank) {
		mTerm = term;
		mRank = rank;
	}
	
	public Term getTerm() {
		return mTerm;
	}

	@Override
	public int getRank() {
		return mRank;
	}

}
