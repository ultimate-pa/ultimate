/* $Id: PhaseEventAutomata.java 409 2009-07-20 14:54:16Z jfaber $
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
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PEAPhaseIndexMap;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.SimpleSet;

public class PhaseEventAutomata implements Comparable<Object> {

	public static final String TIMES = "_X_";

	String mName;
	Phase[] mPhases;
	Phase[] mInit;
	List<String> mClocks;

	// A map of variables and its types to be used in this PEA.
	Map<String, String> mVariables;

	// The set of events used in the PEA.
	Set<String> mEvents;

	// Additional declarations needed when processing this PEA.
	protected List<String> mDeclarations;

	public PhaseEventAutomata(final String name, final Phase[] phases, final Phase[] init) {
		this(name, phases, init, new ArrayList<String>());
	}

	public PhaseEventAutomata(final String name, final Phase[] phases, final Phase[] init, final List<String> clocks) {
		this(name, phases, init, clocks, null, null);
	}

	public PhaseEventAutomata(final String name, final Phase[] phases, final Phase[] init, final List<String> clocks,
			final Map<String, String> variables, final List<String> declarations) {
		this(name, phases, init, clocks, variables, null, declarations);
	}

	/**
	 * @param clocks
	 * @param declarations
	 * @param init
	 * @param name
	 * @param phases
	 * @param variables
	 */
	public PhaseEventAutomata(final String name, final Phase[] phases, final Phase[] init, final List<String> clocks,
			final Map<String, String> variables, final Set<String> events, final List<String> declarations) {
		if (clocks == null) {
			mClocks = new ArrayList<>();
		} else {
			mClocks = clocks;
		}
		mEvents = events;
		mDeclarations = declarations;
		mInit = init;
		mName = name;
		mPhases = phases;
		mVariables = variables;
	}

	public PhaseEventAutomata parallel(final PhaseEventAutomata b) {
		if (b instanceof PEATestAutomaton) {
			return b.parallel(this);
		}
		final List<Phase> newInit = new ArrayList<>();
		final TreeMap<String, Phase> newPhases = new TreeMap<>();

		class TodoEntry {
			Phase p1, p2, p;

			TodoEntry(final Phase p1, final Phase p2, final Phase p) {
				this.p1 = p1;
				this.p2 = p2;
				this.p = p;
			}
		}

		final List<TodoEntry> todo = new LinkedList<>();

		for (int i = 0; i < mInit.length; i++) {
			for (int j = 0; j < b.mInit.length; j++) {
				final CDD sinv = mInit[i].stateInv.and(b.mInit[j].stateInv);
				if (sinv != CDD.FALSE) {
					final CDD cinv = mInit[i].clockInv.and(b.mInit[j].clockInv);
					final Phase p = new Phase(mInit[i].getName() + TIMES + b.mInit[j].getName(), sinv, cinv);

					newInit.add(p);
					newPhases.put(p.getName(), p);
					todo.add(new TodoEntry(mInit[i], b.mInit[j], p));
				}
			}
		}
		while (!todo.isEmpty()) {
			final TodoEntry entry = todo.remove(0);
			final CDD srcsinv = entry.p1.stateInv.and(entry.p2.stateInv);
			final Iterator<?> i = entry.p1.transitions.iterator();
			while (i.hasNext()) {
				final Transition t1 = (Transition) i.next();
				final Iterator<?> j = entry.p2.transitions.iterator();
				while (j.hasNext()) {
					final Transition t2 = (Transition) j.next();

					final CDD guard = t1.guard.and(t2.guard);
					if (guard == CDD.FALSE) {
						continue;
					}
					final CDD sinv = t1.dest.stateInv.and(t2.dest.stateInv);
					// This leads to a serious bug -
					// if (sinv.and(guard) == CDD.FALSE)
					if (sinv == CDD.FALSE) {
						continue;
					}
					if (guard != CDD.TRUE && srcsinv.and(guard).and(sinv.prime()) == CDD.FALSE) {
						continue;
					}
					final CDD cinv = t1.dest.clockInv.and(t2.dest.clockInv);
					final String[] resets = new String[t1.resets.length + t2.resets.length];
					System.arraycopy(t1.resets, 0, resets, 0, t1.resets.length);
					System.arraycopy(t2.resets, 0, resets, t1.resets.length, t2.resets.length);
					final Set<String> stoppedClocks =
							new SimpleSet<>(t1.dest.stoppedClocks.size() + t2.dest.stoppedClocks.size());
					stoppedClocks.addAll(t1.dest.stoppedClocks);
					stoppedClocks.addAll(t2.dest.stoppedClocks);

					final String newname = t1.dest.getName() + TIMES + t2.dest.getName();
					Phase p = newPhases.get(newname);

					if (p == null) {
						p = new Phase(newname, sinv, cinv, stoppedClocks);
						newPhases.put(newname, p);
						todo.add(new TodoEntry(t1.dest, t2.dest, p));
					}
					entry.p.addTransition(p, guard, resets);
				}
			}
		}

		final Phase[] allPhases = newPhases.values().toArray(new Phase[newPhases.size()]);
		final Phase[] initPhases = newInit.toArray(new Phase[newInit.size()]);

		final List<String> newClocks = mergeClockLists(b);

		final Map<String, String> newVariables = mergeVariableLists(b);

		final List<String> newDeclarations = mergeDeclarationLists(b);

		return new PhaseEventAutomata(mName + TIMES + b.mName, allPhases, initPhases, newClocks, newVariables,
				newDeclarations);
	}

	/**
	 * Merges the declaration lists of this automata and the given automata b and returns a new list containing the
	 * result.
	 *
	 * @param b
	 *            automata containing the list to be merged
	 * @return merged list
	 */
	protected List<String> mergeDeclarationLists(final PhaseEventAutomata b) {
		// Merge declarations
		List<String> newDeclarations;
		if (mDeclarations == null) {
			newDeclarations = b.getDeclarations();
		} else if (b.getDeclarations() == null) {
			newDeclarations = mDeclarations;
		} else {
			newDeclarations = new ArrayList<>();
			newDeclarations.addAll(mDeclarations);
			newDeclarations.addAll(b.getDeclarations());
		}
		return newDeclarations;
	}

	/**
	 * Merges the variable lists of this automata and the given automata b and returns a new list containing the merge
	 * result.
	 *
	 * @param b
	 *            automata containing the list to be merged
	 * @return merged list
	 */
	protected Map<String, String> mergeVariableLists(final PhaseEventAutomata b) {
		// Merge variable lists
		final Map<String, String> newVariables;
		if (mVariables == null) {
			newVariables = b.getVariables();
		} else if (b.getVariables() == null) {
			newVariables = mVariables;
		} else {
			newVariables = new HashMap<>();
			for (final String var : mVariables.keySet()) {
				if (b.getVariables().containsKey(var) && !b.getVariables().get(var).equals(mVariables.get(var))) {
					throw new RuntimeException("Different type definitions of " + var + "found!");
				}
				newVariables.put(var, mVariables.get(var));
			}
			newVariables.putAll(b.getVariables());
		}
		return newVariables;
	}

	/**
	 * Merges the clock lists of this automata and the given automata b and returns a new list containing the merge
	 * result.
	 *
	 * @param b
	 *            automata containing the list to be merged
	 * @return merged list
	 */
	protected List<String> mergeClockLists(final PhaseEventAutomata b) {
		// Merge clock lists
		final List<String> newClocks = new ArrayList<>();
		newClocks.addAll(mClocks);
		newClocks.addAll(b.getClocks());
		return newClocks;
	}

	@Override
	public String toString() {
		return mName;
	}

	public void dump() {
		System.err.println("automata " + mName + " { ");
		System.err.print("clocks: ");
		final Iterator<String> clockIter = mClocks.iterator();
		while (clockIter.hasNext()) {
			final String actClock = clockIter.next();
			System.err.print(actClock);
			if (clockIter.hasNext()) {
				System.err.print(", ");
			}
		}
		System.err.println("");
		System.err.print("  init { ");
		String delim = "";
		for (int i = 0; i < mInit.length; i++) {
			System.err.print(delim + mInit[i]);
			delim = ", ";
		}
		System.err.println(" }");
		for (int i = 0; i < mPhases.length; i++) {
			mPhases[i].dump();
		}
		System.err.println("}");
	}

	public void dumpDot() {
		System.out.println("digraph " + mName + " { ");
		for (int i = 0; i < mPhases.length; i++) {
			mPhases[i].dumpDot();
		}
		System.out.println("}");
	}

	/**
	 * @return Returns the init.
	 */
	public Phase[] getInit() {
		return mInit;
	}

	// Ami gefrickel
	public void setInit(final Phase[] init2) {
		mInit = init2;
	}

	/**
	 * @return Returns the name.
	 */
	public String getName() {
		return mName;
	}

	/**
	 * @return Returns the phases.
	 */
	public Phase[] getPhases() {
		return mPhases;
	}

	public List<String> getClocks() {
		return mClocks;
	}

	public void setClocks(final List<String> clocks) {
		mClocks = clocks;
	}

	/**
	 * @return Returns the variables.
	 */
	public Map<String, String> getVariables() {
		return mVariables;
	}

	/**
	 * @return Returns the variables.
	 */
	public Set<String> getEvents() {
		return mEvents;
	}

	/**
	 * @return Returns the declarations.
	 */
	public List<String> getDeclarations() {
		return mDeclarations;
	}

	public void addToClocks(final String clock) {
		mClocks.add(clock);
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(final Object o) {
		return mName.compareTo(((PhaseEventAutomata) o).mName);
	}

	public boolean isEmpty() {
		return getPhases().length <= 0;
	}

	// Change by Ami
	public int getNumberOfLocations() {
		return getPhases().length;
	}

	public Phase getLocation(final int i) {
		return getPhases()[i];
	}

	public void rename() {
		final int locCounter = getNumberOfLocations();
		int counter = 0; // der ist nur aus technischen Gr�nden da: wenn wir zwei zustande st0Xst2 und st2Xst1 haben
		// dann w�rden sonst beide auf st3 umbenannt - das wollen wir nicht, daher dieser counter dazu
		for (int i = 0; i < locCounter; i++) {
			final Phase location = getLocation(i);
			final String[] result = splitForComponents(location.getName());
			int maxIndex = 0;
			for (int j = 0; j < result.length; j++) {
				final String compName = result[j];
				final PEAPhaseIndexMap map = new PEAPhaseIndexMap(compName);
				if (maxIndex < map.getIndex() - 1) {
					maxIndex = map.getIndex() - 1;
				}
			}
			final String newName = "st" + counter + maxIndex;
			counter++;
			location.setName(newName);
		}
	}

	// Splitted einen String location auf, so dass alle Teile, die durch X abgetrennt sind,
	// in einen neuen ArrayString gepackt werden
	private static String[] splitForComponents(final String location) {
		// Create a pattern to match breaks
		final Pattern p = Pattern.compile("_X_");
		// Split input with the pattern
		final String[] result = p.split(location);
		return result;
	}

	// diese Methode vereinfacht die Guards eines PEAS
	// Bsp Guard (A or B) und Stateinvariante des Folgezustands ist (neg B) dann
	// wird der Guard vereinfacht zu (A)
	public void simplifyGuards() {

		final Phase[] phases = getPhases();
		for (int i = 0; i < phases.length; i++) {
			final Phase phase = phases[i];
			final List<Transition> transitions = phase.getTransitions();
			for (int j = 0; j < transitions.size(); j++) {
				final Transition trans = transitions.get(j);
				trans.simplifyGuard();
			}
		}
	}
}
