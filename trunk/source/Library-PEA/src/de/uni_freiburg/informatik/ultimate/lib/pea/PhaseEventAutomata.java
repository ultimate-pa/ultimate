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
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PEAPhaseIndexMap;

public class PhaseEventAutomata<T> implements Comparable<Object> {

	protected final String mName;
	List<Phase<T>> mPhases;
	protected final List<InitialTransition<T>> mInit;
	List<String> mClocks;

	// A map of variables and its types to be used in this PEA.
	Map<String, String> mVariables;

	// The set of events used in the PEA.
	Set<String> mEvents;

	// Additional declarations needed when processing this PEA.
	protected List<String> mDeclarations;

	public PhaseEventAutomata(final String name, final List<Phase<T>> phases, final List<InitialTransition<T>> init) {
		this(name, phases, init, new ArrayList<String>());
	}

	public PhaseEventAutomata(final String name, final List<Phase<T>> phases, final List<InitialTransition<T>> init,
			final List<String> clocks) {
		this(name, phases, init, clocks, null, null);
	}

	public PhaseEventAutomata(final String name, final List<Phase<T>> phases, final List<InitialTransition<T>> init,
			final List<String> clocks, final Map<String, String> variables, final List<String> declarations) {
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
	public PhaseEventAutomata(final String name, final List<Phase<T>> phases, final List<InitialTransition<T>> init,
			final List<String> clocks, final Map<String, String> variables, final Set<String> events,
			final List<String> declarations) {
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

		// add initial transition to Phases in initPhases
		// TODO: remove this, either store all edges in the phases (would be clear) or in the pea, but not both.
		for (InitialTransition<T> initTrans : init) {
			initTrans.getDest().setInitialTransition(initTrans);
		}
	}

	@Override
	public String toString() {
		return mName;
	}

	/**
	 * @return Returns the init.
	 */
	public List<Phase<T>> getInit() {
		List<Phase<T>> initPhases = new ArrayList<>();
		for (InitialTransition<T> t : mInit) {
			initPhases.add(t.getDest());
		}
		return initPhases;
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
	public List<Phase<T>> getPhases() {
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

	@Override
	public int compareTo(final Object o) {
		return mName.compareTo(((PhaseEventAutomata<?>) o).mName);
	}

	public boolean isEmpty() {
		return getPhases().size() <= 0;
	}

	// Change by Ami
	public int getNumberOfLocations() {
		return getPhases().size();
	}

	public Phase<T> getLocation(final int i) {
		return getPhases().get(i);
	}

	public void rename() {
		final int locCounter = getNumberOfLocations();
		int counter = 0; // der ist nur aus technischen Gründen da: wenn wir zwei zustande st0Xst2 und st2Xst1 haben
		// dann würden sonst beide auf st3 umbenannt - das wollen wir nicht, daher dieser counter dazu
		for (int i = 0; i < locCounter; i++) {
			final Phase<T> location = getLocation(i);
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
		final Pattern p = Pattern.compile(PEAUtils.TIMES);
		// Split input with the pattern
		final String[] result = p.split(location);
		return result;
	}

	// diese Methode vereinfacht die Guards eines PEAS
	// Bsp Guard (A or B) und Stateinvariante des Folgezustands ist (neg B) dann
	// wird der Guard vereinfacht zu (A)
	public void simplifyGuards() {
		final List<Phase<T>> phases = getPhases();
		for (int i = 0; i < phases.size(); i++) {
			final Phase<T> phase = phases.get(i);
			final List<Transition<T>> transitions = phase.getTransitions();
			for (int j = 0; j < transitions.size(); j++) {
				final Transition<T> trans = transitions.get(j);
				// trans.simplifyGuard();
				trans.setGuard(PEAUtils.simplifyGuard(trans.getGuard(), phase));
			}
		}
	}

	public boolean isStrict() {
		for (Phase<T> phase : mPhases) {
			if (phase.isStrict() || !phase.getModifiedConstraints().isEmpty()) {
				return true;
			}
		}
		return false;
	}

	public boolean isTotalised() {
		return mName.endsWith(PEAComplement.TOTAL_POSTFIX);
	}

	public boolean isComplemented() {
		return mName.endsWith(PEAComplement.COMPLEMENT_POSTFIX);
	}
}
