/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>

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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.ArrayList;
import java.util.HashSet;

/**
 * build a proposition in CNF of Horn Clauses, using the HornClause3 structure
 *
 * This class is a clauses generation time optimization, because some clauses
 * need not be made at all. (On the other hand, if this is an optimization
 * then probably the client code is not very good ;-))
 *
 * @author stimpflj
 */
public class HornCNFBuilder {
	int numVars;

	int numRequests;  // request counter, to calculate savings later
	boolean solveable;
	private HashSet<HornClause3> clauses;

	int numFalse;
	int numTrue;
	boolean isFalse[];
	boolean isTrue[];

	public HornCNFBuilder(int numVars) {
		this.numVars = numVars;
		numRequests = 0;
		solveable = true;
		isFalse = new boolean[numVars];
		isTrue = new boolean[numVars];
		numFalse = 0;
		numTrue = 0;
		clauses = new HashSet<HornClause3>();
		setFalse(0);
		setTrue(1);
	}

	/**
	 * Get the produced horn clauses.
	 *
	 * If we already figured out that these clauses are not solveable,
	 * <code>null</code> is returned instead.
	 */
	public ArrayList<HornClause3> getClauses() {
		if (!solveable)
			return null;
		ArrayList<HornClause3> out = new ArrayList<HornClause3>();
		out.addAll(clauses);
		for (int i = 0; i < numVars; i++) {
			if (isFalse[i]) out.add(HornClause3.F(i));
			else if (isTrue[i]) out.add(HornClause3.T(i));
		}
		return out;
	}

	/** number of add-clause requests so far */
	public int getNumRequests() {
		return numRequests;
	}

	/** number of actual clauses generated */
	public int getNumClauses() {
		return clauses.size() + numFalse + numTrue;
	}

	/** do we already know that the given variable must be assigned false? */
	public boolean isAlreadyFalse(int x) {
		return isFalse[x];
	}

	public boolean isSolveable() {
		return solveable;
	}

	public void addClauseF(int x) { numRequests++; addF(x); }
	public void addClauseT(int z) { numRequests++; addT(z); }
	public void addClauseFF(int x, int y) { numRequests++; addFF(x, y); }
	public void addClauseFT(int x, int z) { numRequests++; addFT(x, z); }
	public void addClauseFFT(int x, int y, int z) { numRequests++; addFFT(x, y, z); }

	private void setFalse(int x) {
		assert !isTrue[x];
		if (!isFalse[x]) {
			isFalse[x] = true;
			numFalse++;
		}
	}

	private void setTrue(int x) {
		System.err.printf("set %d to true (now %d)\n", x, isTrue[x] ? 1 : 0);
		assert !isFalse[x];
		if (!isTrue[x]) {
			isTrue[x] = true;
			numTrue++;
		}
	}

	private void addClause(HornClause3 c) {
		if (c.l0 > c.l1)
			clauses.add(HornClause3.FFT(c.l1, c.l0, c.l2));
		else
			clauses.add(c);
	}

	private void addF(int x) {
		assert x >= 2;
		if (isFalse[x])
			return;
		else if (isTrue[x])
			solveable = false;
		else {
			setFalse(x);
			/* horn clause will be added when finished, to save memory */
		}
	}

	private void addT(int z) {
		assert z >= 2;
		if (isTrue[z])
			return;
		else if (isFalse[z])
			solveable = false;
		else {
			setTrue(z);
			/* horn clause will be added when finished, to save memory */
		}
	}

	private void addFF(int x, int y) {
		assert x >= 2;
		assert y >= 2;
		if (isFalse[x])
			return;
		else if (isFalse[y])
			return;
		else if (isTrue[x])
			addF(y);
		else if (isTrue[y])
			addF(x);
		else
			addClause(HornClause3.FF(x, y));
	}

	private void addFT(int x, int z) {
		assert x >= 2;
		assert z >= 2;
		if (isFalse[x])
			return;
		else if (isTrue[z])
			return;
		else if (isTrue[x])
			addT(z);
		else if (isFalse[z])
			addF(x);
		else
			addClause(HornClause3.FT(x, z));
	}

	private void addFFT(int x, int y, int z) {
		assert x >= 2;
		assert y >= 2;
		assert z >= 2;
		if (isFalse[x])
			return;
		else if (isFalse[y])
			return;
		else if (isTrue[z])
			return;
		else if (isTrue[x])
			addFT(y, z);
		else if (isTrue[y])
			addFT(x, z);
		else if (isFalse[z])
			addFF(x, y);
		else
			addClause(HornClause3.FFT(x, y, z));
	}
}
