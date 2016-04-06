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

import java.util.Iterator;

public class Horn3Array implements Iterable<Horn3Clause> {

	public static final int FALSEVAR = 0;
	public static final int TRUEVAR = 1;

	private final int numEqVars;

	private IntArray a0;
	private IntArray a1;
	private IntArray a2;

	public Horn3Array(int numEqVars) {
		this.numEqVars = numEqVars;

		a0 = new IntArray();
		a1 = new IntArray();
		a2 = new IntArray();
	}

	public void add(int x, int y, int z) {
		assert 0 <= x && x < numEqVars;
		assert 0 <= y && y < numEqVars;
		assert 0 <= z && z < numEqVars;

		a0.add(x);
		a1.add(y);
		a2.add(z);
	}

	public int size() {
		return a0.size();
	}

	public Horn3Clause get(int idx, Horn3Clause out) {
		if (idx < 0 || idx >= a0.size())
			throw new ArrayIndexOutOfBoundsException();

		out.x = a0.get(idx);
		out.y = a1.get(idx);
		out.z = a2.get(idx);

		return out;
	}

	@Override
	public Iterator<Horn3Clause> iterator() {
		return new Horn3Iterator(this);
	}


	public static class Horn3Iterator implements Iterator<Horn3Clause> {
		private Horn3Array h3a;
		private Horn3Clause h3c;
		private int idx;

		public Horn3Iterator(Horn3Array h3a) {
			this.h3a = h3a;
			this.h3c = new Horn3Clause(-1,-1,-1);
			this.idx = 0;
		}

		@Override
		public boolean hasNext() {
			return idx < h3a.size();
		}

		@Override
		public Horn3Clause next() {
			h3a.get(idx++, h3c);
			return h3c;
		}
	}
}
