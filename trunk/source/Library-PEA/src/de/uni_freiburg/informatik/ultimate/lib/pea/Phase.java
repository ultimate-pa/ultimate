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

public class Phase<T> implements Comparable<Phase<T>> {
	int nr;

	// SR 2010-07-09
	private final boolean isKernel;
	public boolean isInit;
	private final boolean isEntry;
	private final boolean isExit;
	protected final Vector<Transition<T>> incomming;
	String name;
	T stateInv;
	T clockInv;
	final Set<String> stoppedClocks;
	protected final List<Transition<T>> transitions;
	public int ID;

	private boolean mIsTerminal;
	protected boolean mIsStrict;
	protected InitialTransition<T> mInitialTransition;
	// clock constraints that have been modified in the complementation procedure
	// in the case of a phase with a strict clock constraints
	// TODO: dont represent modified constraints as a member of class Phase, data needed by the algorithm should be
	// represented in the algorithm
	// (complementation procedure)
	protected final List<RangeDecision> mModifiedConstraints;

	/**
	 * The phase bits used by the powerset construction. This is only set for automata built from CounterExample traces.
	 */
	PhaseBits phaseBits;

	public Phase(final String name, final T stateInv, final T clockInv, final Set<String> stoppedClocks) {
		this.name = name;
		this.stateInv = stateInv;
		this.clockInv = clockInv;
		transitions = new ArrayList<>();
		this.stoppedClocks = stoppedClocks;

		isKernel = false;
		isInit = false;
		isEntry = false;
		isExit = false;
		incomming = new Vector<>();

		mIsTerminal = true;
		mInitialTransition = null;
		mIsStrict = isStrict(clockInv);
		mModifiedConstraints = new ArrayList<RangeDecision>();
	}

	// TODO: find nicer solution
	protected boolean isStrict(T clockInv) {
		if (clockInv instanceof CDD) {
			return RangeDecision.isStrictLess((CDD) clockInv);
		}
		throw new UnsupportedOperationException();
	}

	public Phase(final String name, final T stateInv, final T clockInv) {
		this(name, stateInv, clockInv, new SimpleSet<String>(0));
	}

	public boolean isInit() {
		return isInit;
	}

	public void setInit(final boolean isInit) {
		this.isInit = isInit;
	}

	public PhaseBits getPhaseBits() {
		return phaseBits;
	}

	public T getStateInvariant() {
		return stateInv;
	}

	public void setStateInvariant(final T inv) {
		stateInv = inv;
	}

	public T getClockInvariant() {
		return clockInv;
	}

	public Set<String> getStoppedClocks() {
		return stoppedClocks;
	}

	public boolean isStopped(final String clock) {
		return stoppedClocks.contains(clock);
	}

	public List<Transition<T>> getTransitions() {
		return transitions;
	}

	public Transition<T> getOutgoingTransition(final Phase<T> dest) {
		Transition<T> result = null;

		for (final Transition<T> transition : transitions) {
			if (transition.getDest().equals(dest)) {
				result = transition;
				break;
			}
		}

		return result;
	}

	/** @return the transition added or modified */
	public Transition<T> addTransition(final Phase<T> dest, final T guard, final String[] resets) {
		final Iterator<Transition<T>> it = transitions.iterator();

		while (it.hasNext()) {
			final Transition<T> t = it.next();

			if ((t.getDest() == dest) && t.getResets().equals(resets)) {
				// t.setGuard(t.getGuard().or(guard));
				t.setGuard(computeOr(t.getGuard(), guard));

				return t;
			}
		}

		final Transition<T> t = new Transition<T>(this, guard, resets, dest);
		transitions.add(t);

		return t;
	}

	// TODO: find nicer solution
	@SuppressWarnings("unchecked")
	protected T computeOr(T a, T b) {
		if (a instanceof CDD && b instanceof CDD) {
			return (T) ((CDD) a).or((CDD) b);
		}
		throw new UnsupportedOperationException();
	}

	@Override
	public String toString() {
		return name;
	}

	/**
	 * @return Returns the name.
	 */
	public String getName() {
		return name;
	}

	public void dump() {
		System.err.println("  state " + this + " { ");

		if (stateInv != CDD.TRUE) {
			System.err.println("    predicate      " + stateInv);
		}

		if (clockInv != CDD.TRUE) {
			System.err.println("    clockinvariant " + clockInv);
		}

		for (final String clock : stoppedClocks) {
			System.err.println("    stopped " + clock);
		}

		System.err.println("    transitions {");

		final Iterator<Transition<T>> it = transitions.iterator();

		while (it.hasNext()) {
			System.err.println("       " + it.next());
		}

		System.err.println("    }");
		System.err.println("  }");
	}

	public void dumpDot() {
		System.out.println("  " + name + " [ label = \"" + stateInv + "\\n" + clockInv + "\" shape=ellipse ]");

		final Iterator<Transition<T>> it = transitions.iterator();

		while (it.hasNext()) {
			final Transition<T> t = it.next();
			System.out.println(
					"  " + t.getSrc().name + " -> " + t.getDest().name + " [ label = \"" + t.getGuard() + "\" ]");
		}
	}

	public String getFlags() {
		String flags = "";

		if (isInit) {
			flags += " Init ";
		}

		if (isKernel) {
			flags += " Kernel ";
		}

		if (isEntry) {
			flags += " Entry ";
		}

		if (isExit) {
			flags += " Exit ";
		}

		return flags;
	}

	// jf
	public void setName(final String name) {
		this.name = name;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(final Phase<T> p) {
		return name.compareTo(p.name);
	}

	public void addIncomming(final Transition<T> trans) {
		incomming.add(trans);
	}

	public void removeIncomming(final Transition<?> trans) {
		incomming.remove(trans);
	}

	public void setID(final int ID) {
		this.ID = ID;
	}

	public int getID() {
		return ID;
	}

	public boolean getTerminal() {
		return mIsTerminal;
	}

	public void setTerminal(final boolean val) {
		mIsTerminal = val;
	}

	public void setInitialTransition(InitialTransition<T> initialTransition) {
		mInitialTransition = initialTransition;
		isInit = true;
	}

	public InitialTransition<T> getInitialTransition() {
		return mInitialTransition;
	}

	public void setModifiedConstraints(List<RangeDecision> modifiedConstraints) {
		mModifiedConstraints.addAll(modifiedConstraints);
	}

	public List<RangeDecision> getModifiedConstraints() {
		return mModifiedConstraints;
	}

	public boolean isStrict() {
		return mIsStrict;
	}
}
