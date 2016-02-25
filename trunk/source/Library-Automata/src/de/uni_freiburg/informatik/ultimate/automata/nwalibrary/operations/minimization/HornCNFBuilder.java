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
	int numRequests;  // request counter, to calculate savings later
	boolean solveable;
	private HashSet<Integer> falseVars;
	private HashSet<Integer> trueVars;
	private HashSet<HornClause3> clauses;

	public HornCNFBuilder() {
		numRequests = 0;
		solveable = true;
		falseVars = new HashSet<Integer>();
		trueVars = new HashSet<Integer>();
		clauses = new HashSet<HornClause3>();
		falseVars.add(0);
		trueVars.add(1);
	}

	/**
	 * Get the produced horn clauses. Make no mistake: This is not a copy. So
	 * don't mutate it, or don't use this HornCNFBuilder instance afterwards.
	 *
	 * If we already figured out that these clauses are not solveable,
	 * <code>null</code> is returned instead.
	 */
	public ArrayList<HornClause3> getClauses() {
		if (!solveable)
			return null;
		ArrayList<HornClause3> out = new ArrayList<HornClause3>();
		out.addAll(clauses);
		return out;
	}

	/** number of add-clause requests so far */
	public int getNumRequests() { return numRequests; }

	/** number of actual clauses generated */
	public int getNumClauses() { return clauses.size(); }

	public void addClauseF(int x) { numRequests++; addF(x); }
	public void addClauseT(int z) { numRequests++; addT(z); }
	public void addClauseFF(int x, int y) { numRequests++; addFF(x, y); }
	public void addClauseFT(int x, int z) { numRequests++; addFT(x, z); }
	public void addClauseFFT(int x, int y, int z) { numRequests++; addFFT(x, y, z); }
	/*
	public void addClauseF(int x) { clauses.add(HornClause3.F(x)); }
	public void addClauseT(int z) { clauses.add(HornClause3.T(z)); }
	public void addClauseFF(int x, int y) { clauses.add(HornClause3.FF(x, y)); }
	public void addClauseFT(int x, int z) { clauses.add(HornClause3.FT(x, z)); }
	public void addClauseFFT(int x, int y, int z) { clauses.add(HornClause3.FFT(x, y, z)); }
	 */

	public boolean isSolveable() {
		return solveable;
	}

	private void addClause(HornClause3 c) {
		if (c.l0 > c.l1)
			clauses.add(HornClause3.FFT(c.l1, c.l0, c.l2));
		else
			clauses.add(c);
	}

	private void addF(int x) {
		assert x >= 2;
		if (falseVars.contains(x))
			return;
		else if (trueVars.contains(x))
			solveable = false;
		else {
			falseVars.add(x);
			addClause(HornClause3.F(x));
		}
	}

	private void addT(int z) {
		assert z >= 2;
		if (trueVars.contains(z))
			return;
		else if (falseVars.contains(z))
			solveable = false;
		else {
			trueVars.add(z);
			addClause(HornClause3.T(z));
		}
	}

	private void addFF(int x, int y) {
		assert x >= 2;
		assert y >= 2;
		if (falseVars.contains(x))
			return;
		else if (falseVars.contains(y))
			return;
		else if (trueVars.contains(x))
			addF(y);
		else if (trueVars.contains(y))
			addF(x);
		else
			addClause(HornClause3.FF(x, y));
	}

	private void addFT(int x, int z) {
		assert x >= 2;
		assert z >= 2;
		if (falseVars.contains(x))
			return;
		else if (trueVars.contains(z))
			return;
		else if (trueVars.contains(x))
			addT(z);
		else if (falseVars.contains(z))
			addF(x);
		else
			addClause(HornClause3.FT(x, z));
	}

	private void addFFT(int x, int y, int z) {
		assert x >= 2;
		assert y >= 2;
		assert z >= 2;
		if (falseVars.contains(x))
			return;
		else if (falseVars.contains(y))
			return;
		else if (trueVars.contains(z))
			return;
		else if (trueVars.contains(x))
			addFT(y, z);
		else if (trueVars.contains(y))
			addFT(x, z);
		else if (falseVars.contains(z))
			addFF(x, y);
		else
			addClause(HornClause3.FFT(x, y, z));
	}
}
