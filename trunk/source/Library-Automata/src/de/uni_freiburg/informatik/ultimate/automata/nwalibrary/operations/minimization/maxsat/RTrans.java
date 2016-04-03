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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat;

/**
 * Return transition for nested word automata (NWA).
 *
 * @author stimpflj
 */
public class RTrans implements Comparable<RTrans> {
	/** Source state */
	public int src;

	/** Return symbol */
	public int sym;

	/** top-of-stack (hierarchical) state */
	public int top;

	/** Destination state */
	public int dst;


	public RTrans() {}

	public RTrans(int src, int sym, int top, int dst)
		{ this.src = src; this.sym = sym; this.top = top; this.dst = dst; }

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof RTrans))
			return false;
		RTrans b = (RTrans) obj;
		return src == b.src && top == b.top && sym == b.sym && dst == b.dst;
	}

	@Override
	public int hashCode() {
		return ((src * 31 + sym) * 31 + top) * 31 + dst;
	}

	@Override
	public int compareTo(RTrans b) {
		return RTrans.compareSrcSymTopDst(this, b);
	}

	public static int compareSrcSymTopDst(RTrans a, RTrans b) {
		if (a.src != b.src) return a.src - b.src;
		if (a.sym != b.sym) return a.sym - b.sym;
		if (a.top != b.top) return a.top - b.top;
		return a.dst - b.dst;
	}

	public static int compareSrcTopSymDst(RTrans a, RTrans b) {
		if (a.src != b.src) return a.src - b.src;
		if (a.top != b.top) return a.top - b.top;
		if (a.sym != b.sym) return a.sym - b.sym;
		return a.dst - b.dst;
	}
}
