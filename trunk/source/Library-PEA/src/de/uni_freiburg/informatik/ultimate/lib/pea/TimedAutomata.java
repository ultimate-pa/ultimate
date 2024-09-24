/* $Id: TimedAutomata.java 227 2006-10-19 07:29:43Z jfaber $
 *
 * This file is part of the PEA tool set
 *
 * The PEA tool set is a collection of tools for
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 *
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

public class TimedAutomata {
	public static final int OP_LT = -2;
	public static final int OP_LTEQ = -1;
	public static final int OP_EQ = 0;
	public static final int OP_GTEQ = 1;
	public static final int OP_GT = 2;
	public static final int OP_NEQ = 4;

	private final Collection<String> mClocks;
	private final State[] mStates;
	private final Map<Phase, Integer> mPhaseNumber = new HashMap<>();

	public TimedAutomata(final PhaseEventAutomata pea, final CDD[] preds, final String[] predNames) {
		mStates = new State[pea.mPhases.size()];
		mClocks = new TreeSet<>();
		for (int i = 0; i < pea.mPhases.size(); i++) {
			mPhaseNumber.put(pea.mPhases.get(i), i);
			mStates[i] = new State();
			mStates[i].nr = i;
			mStates[i].props = "dummy";
			mStates[i].clockInv = filterCDD(pea.mPhases.get(i).getClockInv())[0];
			addClocks(mStates[i].clockInv);
			for (int j = 0; j < preds.length; j++) {
				if (pea.mPhases.get(i).getStateInvariant().and(preds[j]) != CDD.FALSE) {
					mStates[i].props += " " + predNames[j];
				}
			}
		}
		for (final InitialTransition element : pea.mInit) {
			mStates[mPhaseNumber.get(element.getDest())].props += " init";
		}
		for (int i = 0; i < pea.mPhases.size(); i++) {
			final Iterator<Transition> it = pea.mPhases.get(i).getTransitions().iterator();
			final Collection<Edge> edges = new ArrayList<>();
			while (it.hasNext()) {
				final Transition t = it.next();
				final Guard[][] allGuards = filterCDD(t.getGuard());
				for (final Guard[] guard : allGuards) {
					final Edge e = new Edge();
					e.guard = guard;
					e.resets = t.getResets();
					addClocks(e.guard);
					addClocks(e.resets);
					e.dest = mStates[mPhaseNumber.get(t.getDest())];
					edges.add(e);
				}
			}
			mStates[i].edges = edges.toArray(new Edge[edges.size()]);
		}
	}

	private Guard[][] filterCDD(final Guard[] gs, final CDD cdd) {
		if (cdd.getDecision() instanceof RangeDecision
				&& ((RangeDecision) cdd.getDecision()).getVar().indexOf("_X") >= 0) {
			final List<Guard[]> myGuards = new ArrayList<>();
			final String clk = ((RangeDecision) cdd.getDecision()).getVar();
			final int[] limits = ((RangeDecision) cdd.getDecision()).getLimits();
			for (int i = 0; i < cdd.getChilds().length; i++) {
				if (cdd.getChilds()[i] == CDD.FALSE) {
					continue;
				}

				final boolean isEqual = i > 0 && i < cdd.getChilds().length - 1 && limits[i - 1] / 2 == limits[i] / 2;

				final Guard[] ngs =
						new Guard[gs.length + (i == 0 || i == cdd.getChilds().length - 1 || isEqual ? 1 : 2)];
				System.arraycopy(gs, 0, ngs, 0, gs.length);
				int j = gs.length;
				if (i > 0) {
					ngs[j] = new Guard();
					ngs[j].clock = clk;
					ngs[j].cmp = isEqual ? OP_EQ : (limits[i - 1] & 1) == 1 ? OP_GT : OP_GTEQ;
					ngs[j].value = limits[i - 1] / 2;
					j++;
				}
				if (i < cdd.getChilds().length - 1 && !isEqual) {
					ngs[j] = new Guard();
					ngs[j].clock = clk;
					ngs[j].cmp = (limits[i] & 1) == 0 ? OP_LT : OP_LTEQ;
					ngs[j].value = limits[i] / 2;
				}
				final Guard[][] childGuards = filterCDD(ngs, cdd.getChilds()[i]);
				Collections.addAll(myGuards, childGuards);
			}
			return myGuards.toArray(new Guard[myGuards.size()][]);
		}
		if (cdd == CDD.FALSE) {
			return new Guard[0][0];
		}
		if (cdd == CDD.TRUE) {
			final Guard[][] result = new Guard[1][];
			result[0] = gs;
			return result;
		}
		CDD newcdd = CDD.FALSE;
		for (int i = 0; i < cdd.getChilds().length; i++) {
			newcdd = newcdd.or(cdd.getChilds()[i]);
		}
		return filterCDD(gs, newcdd);
	}

	private Guard[][] filterCDD(final CDD cdd) {
		return filterCDD(new Guard[0], cdd);
	}

	private void addClocks(final String[] carr) {
		Collections.addAll(mClocks, carr);
	}

	private void addClocks(final Guard[] guard) {
		for (final Guard element : guard) {
			mClocks.add(element.clock);
		}
	}

	private static String dumpGuard(final Guard[] guard) {
		if (guard.length == 0) {
			return "TRUE";
		}

		final StringBuilder sb = new StringBuilder();
		String delim = "";
		for (final Guard element : guard) {
			sb.append(delim).append(element);
			delim = " and ";
		}
		return sb.toString();
	}

	private static String dumpResets(final String[] resets) {
		if (resets.length == 0) {
			return "";
		}
		final StringBuilder sb = new StringBuilder("RESET{");
		for (final String reset : resets) {
			sb.append(" ").append(reset);
		}
		return sb.append(" }").toString();
	}

	public void dumpKronos() {
		System.out.println("/* Complete System */");
		System.out.println("#locs " + mStates.length);
		int numEdges = 0;
		for (final State mState : mStates) {
			numEdges += mState.edges.length;
		}
		System.out.println("#trans " + numEdges);
		System.out.print("#clocks " + mClocks.size());
		final Iterator<String> it = mClocks.iterator();
		while (it.hasNext()) {
			System.out.print(" " + it.next());
		}
		System.out.println();
		System.out.println("#sync");
		for (int i = 0; i < mStates.length; i++) {
			System.out.println();
			System.out.println("loc: " + i);
			System.out.println("prop: " + mStates[i].props);
			System.out.println("invar: " + dumpGuard(mStates[i].clockInv));
			System.out.println("trans: ");
			for (final Edge e : mStates[i].edges) {
				System.out.println(dumpGuard(e.guard) + " => ; " + dumpResets(e.resets) + "; goto " + e.dest.nr);
			}
		}
	}

	private static class Edge {
		Guard[] guard;
		String[] resets;
		State dest;
	}

	private static class State {
		int nr;
		String props;
		Guard[] clockInv;
		Edge[] edges;
	}

	private static class Guard {
		String clock;
		int cmp;
		int value;

		@Override
		public String toString() {
			String op;
			switch (cmp) {
			case OP_LT:
				op = "<";
				break;
			case OP_LTEQ:
				op = "<=";
				break;
			case OP_EQ:
				op = "==";
				break;
			case OP_GT:
				op = ">";
				break;
			case OP_GTEQ:
				op = ">=";
				break;
			case OP_NEQ:
				op = "!=";
				break;
			default:
				op = "??";
				break;
			}
			return clock + op + value;
		}
	}
}
