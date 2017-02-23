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

/**
 * Save some clauses building up a <code>Horn3Array</code>.
 *
 * @author stimpflj
 */
final class Horn3ArrayBuilder {

	private static final int FALSEVAR = Horn3Clause.FALSEVAR;
	private static final int TRUEVAR = Horn3Clause.TRUEVAR;

	private static final int UNSET = 0;
	private static final int SETFALSE = 1;
	private static final int SETTRUE = 2;

	private Horn3Array mArray;

	/**
	 * for each equivalence variable, UNSET or SETTRUE or SETFALSE
	 */
	private char[] mSingle;

	private boolean mSolveable;

	Horn3ArrayBuilder(int numEqVars) {
		mArray = new Horn3Array(numEqVars);
		mSingle = new char[numEqVars];
		mSolveable = true;
	}

	boolean solveable() {
		return mSolveable;
	}

	boolean isAlreadyFalse(int x) {
		return mSingle[x] == SETFALSE;
	}

	void addClauseFalse(int x) {
		if (mSingle[x] == UNSET) {
			mArray.add(TRUEVAR, x, FALSEVAR);
			mSingle[x] = SETFALSE;
		} else if (mSingle[x] == SETTRUE) {
			mSolveable = false;
		}
	}

	void addClauseTrue(int x) {
		if (mSingle[x] == UNSET) {
			mArray.add(TRUEVAR, TRUEVAR, x);
			mSingle[x] = SETTRUE;
		} else if (mSingle[x] == SETFALSE) {
			mSolveable = false;
		}
	}

	void addClauseFalseFalse(int x, int y) {
		if (x > y) {
			addClauseFalseFalse(y, x);
		} else if (mSingle[x] == SETFALSE) {
			// satisfied
		} else if (mSingle[x] == SETTRUE) {
			addClauseFalse(y);
		} else if (mSingle[y] == SETFALSE) {
			// satisfied
		} else if (mSingle[y] == SETTRUE) {
			addClauseFalse(x);
		} else {
			mArray.add(x, y, FALSEVAR);
		}
	}

	void addClauseFalseTrue(int y, int z) {
		if (mSingle[y] == SETFALSE) {
			// satisfied
		} else if (mSingle[y] == SETTRUE) {
			addClauseTrue(z);
		} else if (mSingle[z] == SETFALSE) {
			addClauseFalse(y);
		} else if (mSingle[z] == SETTRUE) {
			// satisfied
		} else {
			mArray.add(TRUEVAR, y, z);
		}
	}

	void addClauseFalseFalseTrue(int x, int y, int z) {
		if (x > y) {
			addClauseFalseFalseTrue(y, x, z);
		} else if (mSingle[x] == SETFALSE) {
			// satisfied
		} else if (mSingle[x] == SETTRUE) {
			addClauseFalseTrue(y, z);
		} else if (mSingle[y] == SETFALSE) {
			// satisfied
		} else if (mSingle[y] == SETTRUE) {
			addClauseFalseTrue(x, z);
		} else if (mSingle[z] == SETFALSE) {
			addClauseFalseFalse(x, y);
		} else if (mSingle[z] == SETTRUE) {
			// satisfied
		} else {
			mArray.add(x, y, z);
		}
	}

	Horn3Array extract() {
		final Horn3Array result = mSolveable ? mArray : null;

		mArray = null;
		mSingle = null;

		return result;
	}
}
