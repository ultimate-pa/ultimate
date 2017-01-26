package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * Rule of a TreeAutomaton. F(q1, ..., qn) -> p
 * @author mostafa (mostafa.amin93@gmail.com)
 * 
 * @param <LETTER> Letters of the automaton.
 * @param <STATE> States of the automaton.
 */
public class TreeAutomatonRule<LETTER, STATE> {
	private final LETTER mLetter;
	private final List<STATE> mSrc;
	private final STATE mDest;
	
	/**
	 * Construct a rule: letter(src) -> dest
	 * @param letter
	 * @param src
	 * @param dest
	 */
	public TreeAutomatonRule(LETTER letter, List<STATE> src, STATE dest) {
		this.mLetter = letter;
		this.mSrc = src;
		this.mDest = dest;
	}
	
	public List<STATE> getSource() {
		return mSrc;
	}
	public LETTER getLetter() {
		return mLetter;
	}
	public STATE getDest() {
		return mDest;
	}
	public int getArity() {
		return mSrc != null ? mSrc.size() : 0;
	}
	@Override
	public String toString() {
		return "(" + mSrc.toString() + " ~~ " + mLetter.toString() + " ~~> " + mDest.toString() + ")";
	}
	@Override
	public boolean equals(Object x) {
		if (!(x instanceof TreeAutomatonRule)) {
			return false;
		}
		final TreeAutomatonRule<LETTER, STATE> t = (TreeAutomatonRule<LETTER, STATE>) x;
		if (!mDest.equals(t.mDest) || !mLetter.equals(t.mLetter) || t.mSrc.size() != mSrc.size()) {
			return false;
		}
		for (int i = 0; i < mSrc.size(); ++i) {
			if (!mSrc.get(i).equals(t.mSrc.get(i))) {
				return false;
			}
		}
		return true;
	}

	@Override
	public int hashCode() {
		return HashUtils.hashHsieh(31, mDest, mSrc, mLetter);
	}
}
