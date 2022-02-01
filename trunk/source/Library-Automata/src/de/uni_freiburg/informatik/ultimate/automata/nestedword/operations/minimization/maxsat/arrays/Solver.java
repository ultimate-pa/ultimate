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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;

/**
 * Simple SAT solver. Takes a set of Horn clauses. Goes through all variables in sequence, and tries to set each to
 * true.
 * <p>
 * Note that we stick to the convention introduced in HornClause3.java: the variables 0 and 1 are reserved for constant
 * true and false, respectively.
 *
 * @author stimpflj
 */
final class Solver {
	public static final char NONE = 0;
	public static final char TRUE = 1;
	public static final char FALSE = 2;

	private final AutomataLibraryServices mServices;

	/** The number of boolean variables. */
	private final int mNumVars;

	/** The problem in CNF. */
	private final Horn3Array mClauses;

	/** Map variable -> clauses in which it occurs. */
	private final IntArray[] mOccur;

	/** Map variable -> assigned value (NONE, TRUE, FALSE). */
	private final char[] mAssign;

	/** Last assignment operations. */
	private final IntArray mOp;

	/** Pre-allocate a clause to avoid garbage collection overhead. */
	private final Horn3Clause mClause;

	Solver(final AutomataLibraryServices services, final Horn3Array clauses) {
		mServices = services;
		mClauses = clauses;
		mClause = new Horn3Clause(-1, -1, -1);

		// const true and const false
		int numVars = 2;
		for (final Horn3Clause c : clauses) {
			assert 0 <= c.mX;
			assert 0 <= c.mY;
			assert 0 <= c.mZ;

			numVars = Math.max(numVars, c.mX + 1);
			numVars = Math.max(numVars, c.mY + 1);
			numVars = Math.max(numVars, c.mZ + 1);
		}
		mNumVars = numVars;

		mAssign = new char[mNumVars];
		mOp = new IntArray();

		mOccur = new IntArray[mNumVars];
		for (int i = 0; i < mNumVars; i++) {
			mOccur[i] = new IntArray();
		}

		for (int i = 0; i < clauses.size(); i++) {
			clauses.get(i, mClause);

			mOccur[mClause.mX].add(i);
			mOccur[mClause.mY].add(i);
			mOccur[mClause.mZ].add(i);
		}

		for (int i = 0; i < mNumVars; i++) {
			mAssign[i] = NONE;
		}
		mAssign[Horn3Clause.TRUEVAR] = TRUE;
		mAssign[Horn3Clause.FALSEVAR] = FALSE;
	}

	private enum Sat {
		OK,
		UNSATISFIABLE;
	}

	private void setVar(final int v, final char a) {
		assert a != NONE;
		assert mAssign[v] == NONE;
		mOp.add(v);
		mAssign[v] = a;
	}

	private Sat check(final Horn3Clause c) {
		if (mAssign[c.mX] == TRUE && mAssign[c.mY] == TRUE && mAssign[c.mZ] == FALSE) {
			return Sat.UNSATISFIABLE;
		} else if (mAssign[c.mX] == NONE && mAssign[c.mY] == TRUE && mAssign[c.mZ] == FALSE) {
			setVar(c.mX, FALSE);
		} else if (mAssign[c.mX] == TRUE && mAssign[c.mY] == NONE && mAssign[c.mZ] == FALSE) {
			setVar(c.mY, FALSE);
		} else if (mAssign[c.mX] == TRUE && mAssign[c.mY] == TRUE && mAssign[c.mZ] == NONE) {
			setVar(c.mZ, TRUE);
		}
		return Sat.OK;
	}

	private Sat propagate() {
		/* NOTE: the termination condition is "flexible" since the
		 * loop body might insert new elements into `op' */
		for (int i = 0; i < mOp.size(); i++) {
			for (final int c : mOccur[mOp.get(i)]) {
				if (check(mClauses.get(c, mClause)) == Sat.UNSATISFIABLE) {
					return Sat.UNSATISFIABLE;
				}
			}
		}
		return Sat.OK;
	}

	private Sat setAndPropagate(final int v, final char a) {
		assert mOp.size() == 0;
		setVar(v, a);
		if (propagate() == Sat.UNSATISFIABLE) {
			/* rollback */
			for (final int v2 : mOp) {
				mAssign[v2] = NONE;
			}
			mOp.clear();
			return Sat.UNSATISFIABLE;
		}
		mOp.clear();
		return Sat.OK;
	}

	/**
	 * Solve the thing. Call only once, i.e. char[] = new Solver(numVars, theclauses).solve() (Yes, this is a broken
	 * design. But I bet Java is happy to create another object for you.)
	 *
	 * @return <code>null</code> if there is no solution, or an array of assignments (TRUE or FALSE) for each variable.
	 */
	char[] solve() {
		assert mOp.size() == 0;

		for (final Horn3Clause c : mClauses) {
			if (check(c) == Sat.UNSATISFIABLE) {
				return null;
			}
		}
		if (propagate() == Sat.UNSATISFIABLE) {
			return null;
		}
		mOp.clear();

		for (int v = 0; v < mNumVars; v++) {
			if (mAssign[v] == NONE) {
				if (setAndPropagate(v, TRUE) == Sat.UNSATISFIABLE && setAndPropagate(v, FALSE) == Sat.UNSATISFIABLE) {
					/* should not happen */
					assert false;
				}
			}
		}

		/* test */
		for (final Horn3Clause c : mClauses) {
			assert mAssign[c.mX] == FALSE || mAssign[c.mY] == FALSE || mAssign[c.mZ] == TRUE;
		}

		return mAssign;
	}

	private void checkTimeout() throws AutomataOperationCanceledException {
		if (!mServices.getProgressAwareTimer().continueProcessing()) {
			throw new AutomataOperationCanceledException(this.getClass());
		}
	}

//	// "test" the thing
//	public static void main(final String[] args) {
//		Horn3ArrayBuilder builder;
//
//		builder = new Horn3ArrayBuilder(4);
//		builder.addClauseF(3);
//		builder.addClauseFT(2, 3);
//
//		char[] assign;
//		assign = new Solver(builder.extract()).solve();
//		assert assign[2] == FALSE;
//		assert assign[3] == FALSE;
//
//		builder = new Horn3ArrayBuilder(5);
//		builder.addClauseT(2);
//		builder.addClauseFT(2, 3);
//		builder.addClauseFFT(2, 3, 4);
//
//		assign = new Solver(builder.extract()).solve();
//		assert assign[2] == TRUE;
//		assert assign[3] == TRUE;
//		assert assign[4] == TRUE;
//
//		builder = new Horn3ArrayBuilder(5);
//		builder.addClauseT(2);
//		builder.addClauseFT(2, 3);
//		builder.addClauseFFT(2, 3, 4);
//		builder.addClauseF(4);
//
//		assert builder.extract() == null;
//
//		System.err.printf("tests passed%n");
//	}
}
