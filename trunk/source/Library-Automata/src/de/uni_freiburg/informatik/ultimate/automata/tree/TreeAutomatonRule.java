/*
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2014-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * Rule of a TreeAutomaton. F(q1, ..., qn) -> p
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 *
 * @param <LETTER> Letters of the automaton.
 * @param <STATE> States of the automaton.
 */
public class TreeAutomatonRule<LETTER extends IRankedLetter, STATE> {
	private final LETTER mLetter;
	private final List<STATE> mSrc;
	private final STATE mDest;

	/**
	 * Construct a rule: letter(src) -> dest
	 * @param letter
	 * @param src
	 * @param dest
	 */
	public TreeAutomatonRule(final LETTER letter, final List<STATE> src, final STATE dest) {
		 assert letter.getRank() == src.size();
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
		return mLetter.getRank();
	}

	@Override
	public String toString() {
		return "(" + mSrc.toString() + " | " + mLetter.toString() + " | " + mDest.toString() + ")";
	}

	@Override
	public boolean equals(final Object x) {
		if (!(x instanceof TreeAutomatonRule)) {
			return false;
		}
		@SuppressWarnings("unchecked")
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
