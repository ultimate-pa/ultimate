/*
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
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.lib.pea.util.SimpleSet;

/**
 * This class implements a PEA test automaton that is a Phase Event Automaton with final (or bad) locations.
 *
 * @author Johannes Faber
 */
public class PEATestAutomaton extends PhaseEventAutomata<CDD> {

	protected Phase<CDD>[] finalPhases;

	/**
	 * @param name
	 * @param phases
	 * @param init
	 * @param clocks
	 */
	public PEATestAutomaton(final String name, final List<Phase<CDD>> phases, final List<Phase<CDD>> init,
			final List<String> clocks) {
		this(name, phases, init, clocks, new Phase[0]);
	}

	/**
	 * Field constructor.
	 * 
	 * @param name
	 * @param phases
	 * @param init
	 * @param clocks
	 */
	public PEATestAutomaton(final String name, final List<Phase<CDD>> phases, final List<Phase<CDD>> init,
			final List<String> clocks, final Phase<CDD>[] finals) {
		this(name, phases, init, clocks, null, null, finals);
	}

	/**
	 * Field constructor. Fields that are not set remain null.
	 * 
	 * @param name
	 * @param phases
	 * @param init
	 */
	public PEATestAutomaton(final String name, final List<Phase<CDD>> phases, final List<Phase<CDD>> init) {
		super(name, phases, init);
		finalPhases = new Phase[0];
	}

	/**
	 * Constructor initializing all fields.
	 * 
	 * @param name
	 * @param phases
	 * @param init
	 * @param clocks
	 * @param variables
	 * @param declarations
	 * @param finalPhases
	 *            if finalPhases is null then a new Phase array is generated for the final phases
	 */
	public PEATestAutomaton(final String name, final List<Phase<CDD>> phases, final List<Phase<CDD>> init,
			final List<String> clocks, final Map<String, String> variables, final List<String> declarations,
			final Phase<CDD>[] finalPhases) {
		super(name, phases, init, clocks, variables, declarations);
		this.finalPhases = finalPhases != null ? finalPhases : new Phase[0];
	}

	public PEATestAutomaton(final PhaseEventAutomata<CDD> automata) {
		this(automata.mName, automata.mPhases, automata.mInit, automata.mClocks, automata.mVariables,
				automata.mDeclarations, new Phase[0]);
	}

	/**
	 * Computes the parallel product of a test automaton and an arbitrary PEA. If this PEA is also a test automaton then
	 * the new final states are given by tuples of finals states of both components. Otherwise this PEA is not a test
	 * automaton and the new final states are given by the product of final states of the test automaton and normal
	 * states of the PEA.
	 */
	public PEATestAutomaton parallel(final PhaseEventAutomata<CDD> b) {
		final List<Phase<CDD>> newInit = new ArrayList<>();
		final List<Phase<CDD>> newFinal = new ArrayList<>();
		final TreeSet<Phase<CDD>> oldFinal =
				getFinalPhases() == null ? null : new TreeSet<>(Arrays.asList(getFinalPhases()));
		TreeSet<Phase<CDD>> bOldFinal = null;

		final TreeMap<String, Phase<CDD>> newPhases = new TreeMap<>();
		final boolean bIsTestAutomaton = (b instanceof PEATestAutomaton);
		if (bIsTestAutomaton) {
			bOldFinal = new TreeSet<>(Arrays.asList(((PEATestAutomaton) b).getFinalPhases()));
		}

		class TodoEntry {
			Phase<CDD> p1, p2, p;

			TodoEntry(final Phase<CDD> p1, final Phase<CDD> p2, final Phase<CDD> p) {
				this.p1 = p1;
				this.p2 = p2;
				this.p = p;
			}
		}

		final List<TodoEntry> todo = new LinkedList<>();

		for (int i = 0; i < getInit().size(); i++) {
			for (int j = 0; j < b.getInit().size(); j++) {
				final CDD sinv = getInit().get(i).stateInv.and(b.getInit().get(j).stateInv);
				if (sinv != CDD.FALSE) {
					final CDD cinv = getInit().get(i).clockInv.and(b.getInit().get(j).clockInv);
					final Phase<CDD> p = new Phase(
							getInit().get(i).getName() + PEAUtils.TIMES + b.getInit().get(j).getName(), sinv, cinv);
					if (bIsTestAutomaton && oldFinal.contains(getInit().get(i))
							&& bOldFinal.contains(b.getInit().get(j))) {
						newFinal.add(p);
					} else if (!bIsTestAutomaton && oldFinal != null && oldFinal.contains(getInit().get(i))) {
						newFinal.add(p);
					}
					newInit.add(p);
					newPhases.put(p.getName(), p);
					todo.add(new TodoEntry(getInit().get(i), b.getInit().get(j), p));
				}
			}
		}

		while (!todo.isEmpty()) {
			final TodoEntry entry = todo.remove(0);
			final Iterator<Transition<CDD>> i = entry.p1.transitions.iterator();
			while (i.hasNext()) {
				final Transition<CDD> t1 = i.next();
				final Iterator<Transition<CDD>> j = entry.p2.transitions.iterator();
				while (j.hasNext()) {
					final Transition<CDD> t2 = j.next();

					final CDD guard = t1.getGuard().and(t2.getGuard());
					if (guard == CDD.FALSE) {
						continue;
					}
					final CDD sinv = t1.getDest().stateInv.and(t2.getDest().stateInv);
					if (sinv == CDD.FALSE) {
						continue;
					}
					final CDD cinv = t1.getDest().clockInv.and(t2.getDest().clockInv);
					final String[] resets = new String[t1.getResets().length + t2.getResets().length];
					System.arraycopy(t1.getResets(), 0, resets, 0, t1.getResets().length);
					System.arraycopy(t2.getResets(), 0, resets, t1.getResets().length, t2.getResets().length);

					final Set<String> stoppedClocks =
							new SimpleSet<>(t1.getDest().stoppedClocks.size() + t2.getDest().stoppedClocks.size());
					stoppedClocks.addAll(t1.getDest().stoppedClocks);
					stoppedClocks.addAll(t2.getDest().stoppedClocks);

					final String newname = t1.getDest().getName() + PEAUtils.TIMES + t2.getDest().getName();
					Phase<CDD> p = newPhases.get(newname);

					if (p == null) {
						p = new Phase<CDD>(newname, sinv, cinv, stoppedClocks);
						newPhases.put(newname, p);
						todo.add(new TodoEntry(t1.getDest(), t2.getDest(), p));
						if (bIsTestAutomaton && oldFinal != null && bOldFinal != null && oldFinal.contains(t1.getDest())
								&& bOldFinal.contains(t2.getDest())) {
							newFinal.add(p);
						} else if (!bIsTestAutomaton && oldFinal != null && oldFinal.contains(t1.getDest())) {
							newFinal.add(p);
						}

					}
					entry.p.addTransition(p, guard, resets);
				}
			}
		}

		final List<Phase<CDD>> allPhases = (List) newPhases.values();
		final List<Phase<CDD>> initPhases = newInit;
		final Phase<CDD>[] finalPhases = newFinal.toArray(new Phase[newFinal.size()]);

		final List<String> newClocks = PEAUtils.mergeClockLists(this, b);

		final Map<String, String> newVariables = PEAUtils.mergeVariableLists(this, b);

		final List<String> newDeclarations = PEAUtils.mergeDeclarationLists(this, b);

		return new PEATestAutomaton(mName + PEAUtils.TIMES + b.mName, allPhases, initPhases, newClocks, newVariables,
				newDeclarations, finalPhases);
	}

	public Phase<CDD>[] getFinalPhases() {
		return finalPhases;
	}

	public void setFinalPhases(final Phase<CDD>[] finalPhases) {
		this.finalPhases = finalPhases;
	}

	/**
	 * Computes locations that are backward reachable from final locations and replaces all locations that are not
	 * reachable with one new location. Note that we do not simple remove unreachable state to avoid deadlock
	 * introduction in the parallel composition of test automata and model.
	 * 
	 * @return the simplified test automaton
	 */
	public PEATestAutomaton removeUnreachableLocations() {
		// building up map for more efficient access to incoming transitions
		final Map<Phase<CDD>, List<Transition<CDD>>> incomingTrans = new HashMap<>();
		for (final Phase<CDD> phase : mPhases) {
			incomingTrans.put(phase, new ArrayList<Transition<CDD>>());
		}
		for (final Phase<CDD> phase : mPhases) {
			for (final Transition<CDD> transition : phase.getTransitions()) {
				incomingTrans.get(transition.getDest()).add(transition);
			}
		}

		// collect reachable transitions
		final HashSet<Phase> reachablePhases = new HashSet<>();
		final HashSet<Transition> reachableTrans = new HashSet<>();
		List<Phase> unworked = Arrays.asList(getFinalPhases());
		while (!unworked.isEmpty()) {
			final List<Phase> temp = new ArrayList<>();
			for (final Phase phase : unworked) {
				reachablePhases.add(phase);
				for (final Transition trans : incomingTrans.get(phase)) {
					reachableTrans.add(trans);
					if (!reachablePhases.contains(trans.getSrc()) && !unworked.contains(trans.getSrc())) {
						temp.add(trans.getSrc());
					}
				}
			}
			unworked = temp;
		}

		// check if there are unreachable phases
		if (reachablePhases.size() == mPhases.size()) {
			return this;
		}

		// a new phase sinkPhase shall replace the unreachable phases
		final List<Phase<CDD>> newPhases = new ArrayList<>();
		final ArrayList<Phase<CDD>> newInit = new ArrayList<>();
		final Phase<CDD> sinkPhase = new Phase<CDD>("sink", CDD.TRUE, CDD.TRUE);
		newPhases.add(sinkPhase);
		sinkPhase.addTransition(sinkPhase, CDD.TRUE, new String[0]);

		// check if one of the unreachable phases is an inital phase
		boolean initUnreachable = false;
		for (final Phase<CDD> initPhase : mInit) {
			if (reachablePhases.contains(initPhase)) {
				newInit.add(initPhase);
			} else {
				initUnreachable = true;
			}
		}
		if (initUnreachable) {
			newInit.add(sinkPhase);
		}

		// rebuild PEATestAutomaton
		for (final Phase<CDD> phase : mPhases) {
			if (reachablePhases.contains(phase)) {
				newPhases.add(phase);
				final List<Transition<CDD>> removeList = new ArrayList<>();
				for (final Transition<CDD> trans : phase.transitions) {
					if (!reachableTrans.contains(trans)) {
						removeList.add(trans);
					}
				}
				for (final Transition<CDD> trans : removeList) {
					phase.addTransition(sinkPhase, trans.getGuard(), trans.getResets());
					phase.getTransitions().remove(trans);
				}

			} else {
				newInit.remove(phase);
			}
		}

		return new PEATestAutomaton(mName, newPhases, newInit, mClocks, mVariables, mDeclarations, finalPhases);
	}
}
