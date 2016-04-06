/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>
 *
 * Copyright (C) 2016 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat;

public class Horn3ArrayBuilder {

	private static final int FALSEVAR = Horn3Array.FALSEVAR;
	private static final int TRUEVAR = Horn3Array.TRUEVAR;

	private static final int UNSET = 0;
	private static final int SETTRUE = 1;
	private static final int SETFALSE = 2;

	private Horn3Array array;
	private boolean solveable;
	// for each equivalence variable, UNSET or SETTRUE or SETFALSE
	private char[] single;

	public Horn3ArrayBuilder(int numEqVars) {
		array = new Horn3Array(numEqVars);
		single = new char[numEqVars];
		solveable = true;
	}

	public boolean solveable() {
		return solveable;
	}

	public void addClauseF(int x) {
		if (single[x] == UNSET) {
			array.add(x, TRUEVAR, FALSEVAR);
			single[x] = SETFALSE;
		} else if (single[x] == SETTRUE) {
			solveable = false;
		}
	}

	public void addClauseT(int x) {
		if (single[x] == UNSET) {
			array.add(TRUEVAR, TRUEVAR, x);
			single[x] = SETTRUE;
		} else if (single[x] == SETFALSE) {
			solveable = false;
		}
	}

	public void addClauseFF(int x, int y) {
		if (x > y) {
			addClauseFF(y, x);
		} else if (single[x] == SETFALSE) {
			// ok
		} else if (single[x] == SETTRUE) {
			addClauseF(y);
		} else if (single[y] == SETFALSE) {
			// ok
		} else if (single[y] == SETTRUE) {
			addClauseF(x);
		} else {
			array.add(x, y, FALSEVAR);
		}
	}

	public void addClauseFT(int y, int z) {
		if (single[y] == SETFALSE) {
			// ok
		} else if (single[y] == SETTRUE) {
			addClauseT(z);
		} else if (single[z] == SETFALSE) {
			addClauseF(y);
		} else if (single[z] == SETTRUE) {
			// ok
		} else {
			array.add(TRUEVAR, y, z);
		}
	}

	public void addClauseFFT(int x, int y, int z) {
		if (x > y) {
			addClauseFFT(y, x, z);
		} else if (single[x] == SETFALSE) {
			// ok
		} else if (single[x] == SETTRUE) {
			addClauseFT(y, z);
		} else if (single[y] == SETFALSE) {
			// ok
		} else if (single[y] == SETTRUE) {
			addClauseFT(x, z);
		} else if (single[z] == SETFALSE) {
			addClauseFF(x, y);
		} else if (single[z] == SETTRUE) {
			// ok
		} else {
			array.add(x, y, z);
		}
	}

	public Horn3Array extract() {
		Horn3Array result = solveable ? array : null;

		array = null;
		single = null;

		return result;
	}
}
