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

import java.util.ArrayList;
import java.util.HashSet;

/**
 * A Nested Word automaton. There is no distinction between linear and
 * hierarchical states.
 *
 * <p>This is a mostly normalized POD (plain old data) representation of NWAs.
 *
 * <p>The following constraints are useful in most situations:
 * <ul>
 * <li>numStates >= 0 && numISyms >= 0 && numRSyms >= 0
 * <li>isInitial != null && isInitial.length == numStates
 * <li>isFinal != null && isFinal.length == numStates
 * <li>iTrans, cTrans, rTrans are not null and use only symbols and states from
 *     the ranges [0, numStates), [0, numISyms), [0, numCSyms), [0, numRSyms)
 * </ul>
 *
 * <p>This class has static methods to verify these constraints, and also
 * methods to assert determinism.
 *
 * @author stimpflj
 */
class NWA implements Cloneable {
	/** Number of states */
	public int numStates;

	/** Number of internal symbols */
	public int numISyms;

	/** Number of call symbols */
	public int numCSyms;

	/** Number of return symbols */
	public int numRSyms;

	/** For each state whether it is initial */
	public boolean[] isInitial;

	/** For each state whether it is final */
	public boolean[] isFinal;

	/** Internal Transitions */
	public ITrans[] iTrans;

	/** Call Transitions */
	public CTrans[] cTrans;

	/** Return Transitions */
	public RTrans[] rTrans;


	/**
	 * @param nwa readonly <code>NWA</code>
	 *
	 * @return <code>true</code> iff the automaton is consistent
	 */
	public static boolean checkConsistency(NWA nwa) {
		if (nwa.numStates < 0) return false;
		if (nwa.numISyms < 0) return false;
		if (nwa.numRSyms < 0) return false;
		if (nwa.numCSyms < 0) return false;
		if (nwa.isInitial == null || nwa.isInitial.length != nwa.numStates) return false;
		if (nwa.isFinal == null || nwa.isFinal.length != nwa.numStates) return false;
		for (ITrans x : nwa.iTrans) {
			if (x.src < 0 || x.src >= nwa.numStates) return false;
			if (x.sym < 0 || x.sym >= nwa.numISyms) return false;
			if (x.dst < 0 || x.dst >= nwa.numStates) return false;
		}
		for (CTrans x : nwa.cTrans) {
			if (x.src < 0 || x.src >= nwa.numStates) return false;
			if (x.sym < 0 || x.sym >= nwa.numCSyms) return false;
			if (x.dst < 0 || x.dst >= nwa.numStates) return false;
		}
		for (RTrans x : nwa.rTrans) {
			if (x.src < 0 || x.src >= nwa.numStates) return false;
			if (x.sym < 0 || x.sym >= nwa.numRSyms) return false;
			if (x.top < 0 || x.top >= nwa.numStates) return false;
			if (x.dst < 0 || x.dst >= nwa.numStates) return false;
		}
		return true;
	}

	/**
	 * @param nwa readonly <code>NWA</code> which is consistent as by
	 *        <code>checkConsistency()</code>
	 * @return <code>true</code> iff the automaton is deterministic (multiple identical transitions count as non-deterministic)
	 */
	public static boolean checkDeterminism(NWA nwa) {
		HashSet<ITrans> iSeen = new HashSet<ITrans>();
		HashSet<CTrans> cSeen = new HashSet<CTrans>();
		HashSet<RTrans> rSeen = new HashSet<RTrans>();
		for (ITrans x : nwa.iTrans)	if (!iSeen.add(new ITrans(x.src, x.sym, 0))) return false;
		for (CTrans x : nwa.cTrans) if (!cSeen.add(new CTrans(x.src, x.sym, 0))) return false;
		for (RTrans x : nwa.rTrans) if (!rSeen.add(new RTrans(x.src, x.sym, x.top, 0))) return false;
		return true;
	}

	/**
	 * @param nwa a NWA which is consistent as by checkConsistency()
	 * @return ArrayList containing all final states of the nwa, in strictly
	 *         ascending order.
	 */
	public static ArrayList<Integer> computeInitialStates(NWA nwa) {
		ArrayList<Integer> out = new ArrayList<Integer>();
		for (int i = 0; i < nwa.numStates; i++)
			if (nwa.isInitial[i])
				out.add(i);
		return out;
	}

	/**
	 * @param nwa a NWA which is consistent as by checkConsistency
	 * @return ArrayList containing all final states of the nwa, in strictly
	 *         ascending order.
	 */
	public static ArrayList<Integer> computeFinalStates(NWA nwa) {
		ArrayList<Integer> out = new ArrayList<Integer>();
		for (int i = 0; i < nwa.numStates; i++)
			if (nwa.isFinal[i])
				out.add(i);
		return out;
	}

	/**
	 * @return A copy of this NWA instance. No references are shared with the
	 *         instance on which this method is called.
	 */
	@Override
	public NWA clone() {
		NWA out = new NWA();
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
