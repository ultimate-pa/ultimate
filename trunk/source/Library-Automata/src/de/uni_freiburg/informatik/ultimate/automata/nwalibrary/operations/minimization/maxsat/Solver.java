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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat;


/**
 * Simple SAT solver.
 * Takes a set of Horn clauses. Goes through all variables in sequence, and
 * tries to set each to true.
 *
 * Note that we stick to the convention introduced in HornClause3.java:
 * the variables 0 and 1 are reserved for constant true and false,
 * respectively.
 *
 * @author stimpflj
 */
final class Solver {
	static final char NONE = 0;
	static final char TRUE = 1;
	static final char FALSE = 2;

	private static enum Sat { OK, UNSATISFIABLE; };

	/** the number of boolean variables */
	private int numVars;

	/** the problem in CNF */
	private Horn3Array clauses;

	/** variable -> clauses in which it occurs */
	private IntArray[] occur;

	/** variable -> assigned value (NONE, TRUE, FALSE) */
	private char[] assign;

	/** last assignment operations */
	private IntArray op;

	/** pre-allocate a clause to avoid garbage collection overhead */
	private Horn3Clause clause;

	Solver(Horn3Array clauses) {
		this.clauses = clauses;
		this.clause = new Horn3Clause(-1,-1,-1);

		numVars = 2; // const true and const false
		for (Horn3Clause c : clauses) {
			assert 0 <= c.x;
			assert 0 <= c.y;
			assert 0 <= c.z;

			numVars = Math.max(numVars, c.x + 1);
			numVars = Math.max(numVars, c.y + 1);
			numVars = Math.max(numVars, c.z + 1);
		}

		assign = new char[numVars];
		op = new IntArray();

		occur = new IntArray[numVars];
		for (int i = 0; i < numVars; i++)
			occur[i] = new IntArray();

		for (int i = 0; i < clauses.size(); i++) {
			clauses.get(i, clause);

			occur[clause.x].add(i);
			occur[clause.y].add(i);
			occur[clause.z].add(i);
		}

		for (int i = 0; i < numVars; i++)
			assign[i] = NONE;
		assign[Horn3Clause.TRUEVAR] = TRUE;
		assign[Horn3Clause.FALSEVAR] = FALSE;
	}

	private void setVar(int v, char a) {
		assert a != NONE;
		assert assign[v] == NONE;
		op.add(v);
		assign[v] = a;
	}

	private Sat check(Horn3Clause c) {
		if (assign[c.x] == TRUE &&
			assign[c.y] == TRUE &&
			assign[c.z] == FALSE)
			return Sat.UNSATISFIABLE;
		else if (assign[c.x] == NONE &&
				 assign[c.y] == TRUE &&
				 assign[c.z] == FALSE)
			setVar(c.x, FALSE);
		else if (assign[c.x] == TRUE &&
				 assign[c.y] == NONE &&
				 assign[c.z] == FALSE)
			setVar(c.y, FALSE);
		else if (assign[c.x] == TRUE &&
				 assign[c.y] == TRUE &&
				 assign[c.z] == NONE)
			setVar(c.z, TRUE);
		return Sat.OK;
	}

	private Sat propagate() {
		/* NOTE: the termination condition is "flexible" since the
		 * loop body might insert new elements into `op' */
		for (int i = 0; i < op.size(); i++) {
			for (int c : occur[op.get(i)]) {
				if (check(clauses.get(c, clause)) == Sat.UNSATISFIABLE) {
					return Sat.UNSATISFIABLE;
				}
			}
		}
		return Sat.OK;
	}

	private Sat setAndPropagate(int v, char a) {
		assert op.size() == 0;
		setVar(v, a);
		if (propagate() == Sat.UNSATISFIABLE) {
			/* rollback */
			for (int v2 : op)
				assign[v2] = NONE;
			op.clear();
			return Sat.UNSATISFIABLE;
		}
		op.clear();
		return Sat.OK;
	}

	/**
	 * Solve the thing. Call only once, i.e.
	 *
	 * char[] = new Solver(numVars, theclauses).solve()
	 *
	 * (Yes, this is a broken design. But I bet Java is happy to create
	 * another object for you.)
	 *
	 * @return <code>null</code> if there is no solution, or an array
	 * of assignments (TRUE or FALSE) for each variable.
	 */
	char[] solve() {
		assert op.size() == 0;

		for (Horn3Clause c : clauses)
			if (check(c) == Sat.UNSATISFIABLE)
				return null;
		if (propagate() == Sat.UNSATISFIABLE)
			return null;
		op.clear();

		for (int v = 0; v < numVars; v++) {
			if (assign[v] == NONE) {
				if (setAndPropagate(v, TRUE) == Sat.UNSATISFIABLE
					&& setAndPropagate(v, FALSE) == Sat.UNSATISFIABLE) {
					/* should not happen */
					assert false;
				}
			}
		}

		/* test */
		for (Horn3Clause c : clauses) {
			assert assign[c.x] == FALSE
					|| assign[c.y] == FALSE
					|| assign[c.z] == TRUE;
		}

		return assign;
	}


	// "test" the thing
	public static void main(String[] args) {
		char assign[];
		Horn3ArrayBuilder builder;

		builder = new Horn3ArrayBuilder(4);
		builder.addClauseF(3);
		builder.addClauseFT(2, 3);

		assign = new Solver(builder.extract()).solve();
		assert assign[2] == FALSE;
		assert assign[3] == FALSE;

		builder = new Horn3ArrayBuilder(5);
		builder.addClauseT(2);
		builder.addClauseFT(2, 3);
		builder.addClauseFFT(2, 3, 4);

		assign = new Solver(builder.extract()).solve();
		assert assign[2] == TRUE;
		assert assign[3] == TRUE;
		assert assign[4] == TRUE;

		builder = new Horn3ArrayBuilder(5);
		builder.addClauseT(2);
		builder.addClauseFT(2, 3);
		builder.addClauseFFT(2, 3, 4);
		builder.addClauseF(4);

		assert builder.extract() == null;

		System.err.printf("tests passed\n");
	}
}
