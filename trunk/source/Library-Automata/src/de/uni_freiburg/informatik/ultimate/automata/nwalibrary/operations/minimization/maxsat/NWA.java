/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>

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

import java.util.ArrayList;
import java.util.HashSet;

/**
 * A Nested Word automaton. There is no distinction between linear and
 * hierarchical states.
 *
 * <p>
 * This is a mostly normalized POD (plain old data) representation of NWAs.
 *
 * <p>
 * The following constraints are useful in most situations:
 *
 * <ul>
 * <li>numStates &ge; 0 && numISyms &ge; 0 && numRSyms &ge; 0
 * <li>isInitial &ne; null && isInitial.length = numStates
 * <li>isFinal &ne; null && isFinal.length = numStates
 * <li>iTrans, cTrans, rTrans are not null and use only symbols and states from
 * the ranges [0, numStates), [0, numISyms), [0, numCSyms), [0, numRSyms)
 * </ul>
 *
 * <p>
 * This class has static methods to verify these constraints, and also methods
 * to assert determinism.
 *
 * @author stimpflj
 */
final class NWA implements Cloneable {
	/** Number of states */
	int numStates;

	/** Number of internal symbols */
	int numISyms;

	/** Number of call symbols */
	int numCSyms;

	/** Number of return symbols */
	int numRSyms;

	/** For each state whether it is initial */
	boolean[] isInitial;

	/** For each state whether it is final */
	boolean[] isFinal;

	/** Internal Transitions */
	ITrans[] iTrans;

	/** Call Transitions */
	CTrans[] cTrans;

	/** Return Transitions */
	RTrans[] rTrans;


	/**
	 * @param nwa readonly <code>NWA</code>
	 *
	 * @return <code>true</code> iff the automaton is consistent
	 */
	static boolean checkConsistency(NWA nwa) {
		if (nwa.numStates < 0) {
			return false;
		}
		if (nwa.numISyms < 0) {
			return false;
		}
		if (nwa.numRSyms < 0) {
			return false;
		}
		if (nwa.numCSyms < 0) {
			return false;
		}

		if (nwa.isInitial == null || nwa.isInitial.length != nwa.numStates) {
			return false;
		}
		if (nwa.isFinal == null || nwa.isFinal.length != nwa.numStates) {
			return false;
		}

		for (final ITrans x : nwa.iTrans) {
			if (x.src < 0 || x.src >= nwa.numStates) {
				return false;
			}
			if (x.sym < 0 || x.sym >= nwa.numISyms) {
				return false;
			}
			if (x.dst < 0 || x.dst >= nwa.numStates) {
				return false;
			}
		}
		for (final CTrans x : nwa.cTrans) {
			if (x.src < 0 || x.src >= nwa.numStates) {
				return false;
			}
			if (x.sym < 0 || x.sym >= nwa.numCSyms) {
				return false;
			}
			if (x.dst < 0 || x.dst >= nwa.numStates) {
				return false;
			}
		}
		for (final RTrans x : nwa.rTrans) {
			if (x.src < 0 || x.src >= nwa.numStates) {
				return false;
			}
			if (x.sym < 0 || x.sym >= nwa.numRSyms) {
				return false;
			}
			if (x.top < 0 || x.top >= nwa.numStates) {
				return false;
			}
			if (x.dst < 0 || x.dst >= nwa.numStates) {
				return false;
			}
		}

		return true;
	}

	/**
	 * @param nwa
	 *            readonly <code>NWA</code> which is consistent as by
	 *            <code>checkConsistency()</code>
	 * @return <code>true</code> iff the automaton is deterministic (multiple
	 *         identical transitions count as non-deterministic)
	 */
	static boolean checkDeterminism(NWA nwa) {
		final HashSet<ITrans> iSeen = new HashSet<ITrans>();
		final HashSet<CTrans> cSeen = new HashSet<CTrans>();
		final HashSet<RTrans> rSeen = new HashSet<RTrans>();

		for (final ITrans x : nwa.iTrans) {
			if (!iSeen.add(new ITrans(x.src, x.sym, 0))) {
				return false;
			}
		}
		for (final CTrans x : nwa.cTrans) {
			if (!cSeen.add(new CTrans(x.src, x.sym, 0))) {
				return false;
			}
		}
		for (final RTrans x : nwa.rTrans) {
			if (!rSeen.add(new RTrans(x.src, x.sym, x.top, 0))) {
				return false;
			}
		}

		return true;
	}

	/**
	 * @param nwa
	 *            a NWA which is consistent as by checkConsistency()
	 * @return ArrayList containing all final states of <code>nwa</code>, in
	 *         strictly ascending order.
	 */
	static ArrayList<Integer> computeInitialStates(NWA nwa) {
		final ArrayList<Integer> out = new ArrayList<Integer>();

		for (int i = 0; i < nwa.numStates; i++) {
			if (nwa.isInitial[i]) {
				out.add(i);
			}
		}

		return out;
	}

	/**
	 * @param nwa
	 *            an NWA which is consistent as by checkConsistency
	 * @return ArrayList containing all final states of <code>nwa</code>, in
	 *         strictly ascending order.
	 */
	static ArrayList<Integer> computeFinalStates(NWA nwa) {
		final ArrayList<Integer> out = new ArrayList<Integer>();

		for (int i = 0; i < nwa.numStates; i++) {
			if (nwa.isFinal[i]) {
				out.add(i);
			}
		}

		return out;
	}

	/**
	 * @return A copy of this NWA instance. No references are shared with the
	 *         instance on which this method is called.
	 */
	@Override
	public NWA clone() {
		final NWA out = new NWA();
		out.numStates = numStates;
		out.numISyms = numISyms;
		out.numCSyms = numCSyms;
		out.numRSyms = numRSyms;
		out.isInitial = isInitial.clone();
		out.isFinal = isFinal.clone();
		out.iTrans = iTrans.clone();
		out.cTrans = cTrans.clone();
		out.rTrans = rTrans.clone();

		return out;
	}
}


/**
 * Call transition for nested word automata (NWA).
 *
 * @author stimpflj
 */
final class ITrans {
	/** Source state */
	int src;

	/** Internal symbol */
	int sym;

	/** Destination state */
	int dst;


	ITrans() {}

	ITrans(int src, int sym, int dst) {
		this.src = src;
		this.sym = sym;
		this.dst = dst;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == null || !(obj instanceof ITrans)) {
			return false;
		}

		final ITrans b = (ITrans) obj;
		return src == b.src && sym == b.sym && dst == b.dst;
	}

	@Override
	public int hashCode() {
		return (src * 31 + sym) * 31 + dst;
	}

	static int compareSrcSymDst(ITrans a, ITrans b) {
		if (a.src != b.src) {
			return a.src - b.src;
		}
		if (a.sym != b.sym) {
			return a.sym - b.sym;
		}
		return a.dst - b.dst;
	}
}


/**
 * Call transition for nested word automata (NWA)
 *
 * @author stimpflj
 */
final class CTrans {
	/** Source state */
	int src;

	/** Call symbol */
	int sym;

	/** Destination state */
	int dst;

	CTrans() {}

	CTrans(int src, int sym, int dst) {
		this.src = src;
		this.sym = sym;
		this.dst = dst;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == null || !(obj instanceof CTrans)) {
			return false;
		}

		final CTrans b = (CTrans) obj;

		return src == b.src && sym == b.sym && dst == b.dst;
	}

	@Override
	public int hashCode() {
		return (src * 31 + sym) * 31 + dst;
	}

	static int compareSrcSymDst(CTrans a, CTrans b) {
		if (a.src != b.src) {
			return a.src - b.src;
		}
		if (a.sym != b.sym) {
			return a.sym - b.sym;
		}
		return a.dst - b.dst;
	}
}


/**
 * Return transition for nested word automata (NWA).
 *
 * @author stimpflj
 */
final class RTrans {
	/** Source state */
	int src;

	/** Return symbol */
	int sym;

	/** top-of-stack (hierarchical) state */
	int top;

	/** Destination state */
	int dst;


	RTrans() {}

	RTrans(int src, int sym, int top, int dst) {
		this.src = src;
		this.sym = sym;
		this.top = top;
		this.dst = dst;
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof RTrans)) {
			return false;
		}

		final RTrans b = (RTrans) obj;

		return src == b.src && top == b.top && sym == b.sym && dst == b.dst;
	}

	@Override
	public int hashCode() {
		return ((src * 31 + sym) * 31 + top) * 31 + dst;
	}

	static int compareSrcSymTopDst(RTrans a, RTrans b) {
		if (a.src != b.src) {
			return a.src - b.src;
		}
		if (a.sym != b.sym) {
			return a.sym - b.sym;
		}
		if (a.top != b.top) {
			return a.top - b.top;
		}
		return a.dst - b.dst;
	}

	static int compareSrcTopSymDst(RTrans a, RTrans b) {
		if (a.src != b.src) {
			return a.src - b.src;
		}
		if (a.top != b.top) {
			return a.top - b.top;
		}
		if (a.sym != b.sym) {
			return a.sym - b.sym;
		}
		return a.dst - b.dst;
	}
}