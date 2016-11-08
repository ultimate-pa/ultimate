/*
 * Copyright (C) 2015 Dirk Steinmetz
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

/**
 * Class representing a control flow graph. A control flow graph consists of
 * nodes ("locations") connected by edges ("transitions").
 * 
 * Each location represents a specific program state, while each transition
 * represents a step in the program (for example an instruction or a condition).
 */
public final class ControlFlowGraph {

	private final Location entry;
	private final Location exit;
	private final Map<Location, Collection<Transition>> locations;
	private final Collection<Transition> transitions;

	/**
	 * A node in the control flow graph.
	 */
	public static final class Location {
		private final BoogieIcfgLocation programPoint;

		/**
		 * Creates a new location on a given program point.
		 * 
		 * @param programPoint
		 *            the program point the locations is at
		 */
		public Location(final BoogieIcfgLocation programPoint) {
			this.programPoint = programPoint;
		}

		/**
		 * Returns the program point associated with the given location.
		 * 
		 * @return program point associated with this location
		 */
		public BoogieIcfgLocation getProgramPoint() {
			return programPoint;
		}

		@Override
		public String toString() {
			return programPoint.toString();
		}
		
		
	}

	/**
	 * An edge in the control flow graph.
	 */
	public static final class Transition {
		private final UnmodifiableTransFormula transFormula;
		private final Location start;
		private final Location end;

		/**
		 * Creates a new transition between two locations.
		 * 
		 * @param transFormula
		 *            the TransFormula defining the behavior of the transition
		 * @param start
		 *            the location the transition starts from
		 * @param end
		 *            the location the transition finishes at
		 */
		public Transition(final UnmodifiableTransFormula transFormula,
				final Location start, final Location end) {
			this.transFormula = transFormula;
			this.start = start;
			this.end = end;
		}

		/**
		 * Returns the {@link UnmodifiableTransFormula} defining the behavior of the
		 * transition.
		 * 
		 * @return TransFormula defining the behvaiour of the transition
		 */
		public UnmodifiableTransFormula getTransFormula() {
			return transFormula;
		}

		/**
		 * Returns the location the transition starts from
		 * 
		 * @return location the transition starts from
		 */
		public Location getStart() {
			return start;
		}

		/**
		 * Returns the location the transition finishes at.
		 * 
		 * @return location the transition finishes at
		 */
		public Location getEnd() {
			return end;
		}

		@Override
		public String toString() {
			return "Transition from=" + start + " to=" + end + ", transFormula=" + transFormula;
		}
		
		
	}

	/**
	 * Creates a control flow graph based on given locations and transitions.
	 * 
	 * It is impossible to have a CFG containing the same location multiple
	 * times. If a location occurs multiple times in a collection, all but one
	 * occurrence will be discarded.
	 * 
	 * @param entry
	 *            the initial location
	 * @param exit
	 *            the final location
	 * @param locations
	 *            a collection of all locations within the graph. Must contain
	 *            all locations references by transitions as well as entry and
	 *            exit
	 * @param transitions
	 *            a collection of all transitions within the graph
	 */
	public ControlFlowGraph(final Location entry, final Location exit,
			final Collection<Location> locations,
			final Collection<Transition> transitions) {
		this.entry = entry;
		this.exit = exit;
		final Map<Location,Collection<Transition>> innerLocations =
				new HashMap<>(locations.size());
		for (final Location location : locations) {
			innerLocations.put(location, new ArrayList<Transition>());
		}
		for (final Transition transition: transitions) {
			final Collection<Transition> startCol =
					innerLocations.get(transition.getStart());
			if (startCol == null) {
				throw new IllegalArgumentException("Tried to construct CFG "
						+ "with transitions originating in locations outside "
						+ "of the CFG.");
			}
			startCol.add(transition);
		}
		this.locations = Collections.unmodifiableMap(innerLocations);
		final Collection<Transition> innerTransitions = new ArrayList<>(
				transitions.size());
		innerTransitions.addAll(transitions);
		this.transitions = Collections.unmodifiableCollection(innerTransitions);
	}

	/**
	 * Returns the initial location of the graph.
	 * 
	 * @return initial location
	 */
	public Location getEntry() {
		return entry;
	}

	/**
	 * Returns the final location of the graph.
	 * 
	 * @return final location
	 */
	public Location getExit() {
		return exit;
	}

	/**
	 * Returns a set of all locations within the graph. Immutable. 
	 * 
	 * @return immutable set of all locations
	 */
	public Set<Location> getLocations() {
		return locations.keySet();
	}

	/**
	 * Returns a collection of all transitions within the graph. Immutable.
	 * 
	 * @return immutable collection of all transitions
	 */
	public Collection<Transition> getTransitions() {
		return transitions;
	}

	/**
	 * Returns a collection of all transitions originating in a given location.
	 * 
	 * @param location
	 *            the location to get originating transitions for, must be
	 *            contained in this CFG
	 * @return collection of all transitions originating in location
	 */
	public Collection<Transition> getTransitionsForLocation(
			final Location location) {
		return locations.get(location);
	}
}
