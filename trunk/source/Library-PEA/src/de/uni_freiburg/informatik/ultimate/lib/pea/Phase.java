/* $Id: Phase.java 307 2008-07-29 16:03:20Z jfaber $
 *
 * This file is part of the PEA tool set
 *
 * The PEA tool set is a collection of tools for Phase Event Automata
 * (PEA).
 *
 * Copyright (C) 2005-2006, Carl von Ossietzky University of Oldenburg
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
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Vector;

import de.uni_freiburg.informatik.ultimate.lib.pea.util.SimpleSet;

public class Phase implements Comparable<Phase> {

	private final boolean mIsKernel;
	private boolean mIsInit;
	private final boolean mIsEntry;
	private final boolean mIsExit;
	private final List<Transition> mIncomming;
	private String mName;
	private CDD mStateInv;
	private CDD mClockInv;
	private final Set<String> mStoppedClocks;
	private final List<Transition> mTransitions;

	private boolean mIsTerminal;
	private final boolean mIsStrict;
	private InitialTransition mInitialTransition;
	// clock constraints that have been modified in the complementation procedure
	// in the case of a phase with a strict clock constraints
	private final List<RangeDecision> mModifiedConstraints;

	/**
	 * The phase bits used by the powerset construction. This is only set for automata built from CounterExample traces.
	 */
	PhaseBits phaseBits;

	public Phase(final String name, final CDD stateInv, final CDD clockInv, final Set<String> stoppedClocks) {
		mName = name;
		setStateInv(stateInv);
		setClockInv(clockInv);
		mTransitions = new ArrayList<>();
		mStoppedClocks = stoppedClocks;

		mIsKernel = false;
		mIsInit = false;
		mIsEntry = false;
		mIsExit = false;
		mIncomming = new Vector<>();

		mIsTerminal = true;
		mInitialTransition = null;
		mIsStrict = RangeDecision.isStrictLess(clockInv);
		mModifiedConstraints = new ArrayList<>();
	}

	public Phase(final String name, final CDD stateInv, final CDD clockInv) {
		this(name, stateInv, clockInv, new SimpleSet<String>(0));
	}

	public Phase(final String name, final CDD stateInv) {
		this(name, stateInv, CDD.TRUE);
	}

	public Phase(final String name) {
		this(name, CDD.TRUE, CDD.TRUE);
	}

	public boolean isInit() {
		return mIsInit;
	}

	public void setInit(final boolean isInit) {
		mIsInit = isInit;
	}

	public PhaseBits getPhaseBits() {
		return phaseBits;
	}

	public CDD getStateInvariant() {
		return getStateInv();
	}

	public void setStateInvariant(final CDD inv) {
		setStateInv(inv);
	}

	public CDD getClockInvariant() {
		return getClockInv();
	}

	public Set<String> getStoppedClocks() {
		return mStoppedClocks;
	}

	public boolean isStopped(final String clock) {
		return getStoppedClocks().contains(clock);
	}

	public List<Transition> getTransitions() {
		return mTransitions;
	}

	public Transition getOutgoingTransition(final Phase dest) {
		Transition result = null;

		for (final Transition transition : getTransitions()) {
			if (transition.getDest().equals(dest)) {
				result = transition;
				break;
			}
		}

		return result;
	}

	/** @return the transition added or modified */
	public Transition addTransition(final Phase dest, final CDD guard, final String[] resets) {
		final Iterator<Transition> it = getTransitions().iterator();

		while (it.hasNext()) {
			final Transition t = it.next();

			if (t.getDest() == dest && t.getResets().equals(resets)) {
				t.setGuard(t.getGuard().or(guard));

				return t;
			}
		}

		final Transition t = new Transition(this, guard, resets, dest);
		getTransitions().add(t);

		return t;
	}

	@Override
	public String toString() {
		return mName;
	}

	/**
	 * @return Returns the name.
	 */
	public String getName() {
		return mName;
	}

	public void dump() {
		System.err.println("  state " + this + " { ");

		if (getStateInv() != CDD.TRUE) {
			System.err.println("    predicate      " + getStateInv());
		}

		if (getClockInv() != CDD.TRUE) {
			System.err.println("    clockinvariant " + getClockInv());
		}

		for (final String clock : getStoppedClocks()) {
			System.err.println("    stopped " + clock);
		}

		System.err.println("    transitions {");

		final Iterator<Transition> it = getTransitions().iterator();

		while (it.hasNext()) {
			System.err.println("       " + it.next());
		}

		System.err.println("    }");
		System.err.println("  }");
	}

	public void dumpDot() {
		System.out
				.println("  " + mName + " [ label = \"" + getStateInv() + "\\n" + getClockInv() + "\" shape=ellipse ]");

		final Iterator<Transition> it = getTransitions().iterator();

		while (it.hasNext()) {
			final Transition t = it.next();
			System.out.println(
					"  " + t.getSrc().mName + " -> " + t.getDest().mName + " [ label = \"" + t.getGuard() + "\" ]");
		}
	}

	public String getFlags() {
		final StringBuilder flags = new StringBuilder();

		if (mIsInit) {
			flags.append(" Init ");
		}

		if (mIsKernel) {
			flags.append(" Kernel ");
		}

		if (mIsEntry) {
			flags.append(" Entry ");
		}

		if (mIsExit) {
			flags.append(" Exit ");
		}

		return flags.toString();
	}

	public void setName(final String name) {
		mName = name;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(final Phase p) {
		return mName.compareTo(p.mName);
	}

	public void addIncomming(final Transition trans) {
		mIncomming.add(trans);
	}

	public void removeIncomming(final Transition trans) {
		mIncomming.remove(trans);
	}

	public boolean getTerminal() {
		return mIsTerminal;
	}

	public void setTerminal(final boolean val) {
		mIsTerminal = val;
	}

	public void setInitialTransition(final InitialTransition initialTransition) {
		mInitialTransition = initialTransition;
		mIsInit = true;
	}

	public void setModifiedConstraints(final List<RangeDecision> modifiedConstraints) {
		mModifiedConstraints.addAll(modifiedConstraints);
	}

	public List<RangeDecision> getModifiedConstraints() {
		return mModifiedConstraints;
	}

	public boolean isStrict() {
		return mIsStrict;
	}

	public CDD getStateInv() {
		return mStateInv;
	}

	public void setStateInv(final CDD stateInv) {
		mStateInv = stateInv;
	}

	public CDD getClockInv() {
		return mClockInv;
	}

	public void setClockInv(final CDD clockInv) {
		mClockInv = clockInv;
	}

	public InitialTransition getInitialTransition() {
		return mInitialTransition;
	}
}
