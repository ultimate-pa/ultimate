/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>
 *
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
 * General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see
 * <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automata Library, or any covered work, by linking or combining it
 * with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE Automata Library grant you additional permission to convey the
 * resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.arrays;

import java.util.Iterator;

/**
 * Array of Horn clauses with at most three literals.
 *
 * @author stimpflj
 */
final class Horn3Array implements Iterable<Horn3Clause> {

	private final int mNumVars;

	private final IntArray mAx;
	private final IntArray mAy;
	private final IntArray mAz;

	Horn3Array(final int numVars) {
		mNumVars = numVars;

		mAx = new IntArray();
		mAy = new IntArray();
		mAz = new IntArray();
	}

	void add(final int x, final int y, final int z) {
		assert 0 <= x && x < mNumVars;
		assert 0 <= y && y < mNumVars;
		assert 0 <= z && z < mNumVars;

		mAx.add(x);
		mAy.add(y);
		mAz.add(z);
	}

	int size() {
		return mAx.size();
	}

	Horn3Clause get(final int idx, final Horn3Clause out) {
		if (idx < 0 || idx >= mAx.size()) {
			throw new ArrayIndexOutOfBoundsException();
		}

		out.mX = mAx.get(idx);
		out.mY = mAy.get(idx);
		out.mZ = mAz.get(idx);

		return out;
	}

	@Override
	public Iterator<Horn3Clause> iterator() {
		return new Horn3Iterator(this);
	}

	/**
	 * Iterate over all clauses of an <code>Horn3Array</code>. For efficiency, each iteration returns the same
	 * pre-allocated Horn3Clause, modified to contain the values of the current clause. The caller must make a copy if
	 * the clause is used longer.
	 *
	 * @author stimpflj
	 */
	private static final class Horn3Iterator implements Iterator<Horn3Clause> {

		private final Horn3Clause mH3c;
		private final Horn3Array mH3a;
		private int mIdx;

		Horn3Iterator(final Horn3Array h3a) {
			mH3a = h3a;
			mH3c = new Horn3Clause(-1, -1, -1);
			mIdx = 0;
		}

		@Override
		public boolean hasNext() {
			return mIdx < mH3a.size();
		}

		@Override
		public Horn3Clause next() {
			mH3a.get(mIdx++, mH3c);
			return mH3c;
		}
	}
}
