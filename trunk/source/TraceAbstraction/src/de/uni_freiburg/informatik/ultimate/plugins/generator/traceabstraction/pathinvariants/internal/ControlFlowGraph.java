package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;

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
	private final Collection<Location> locations;
	private final Collection<Transition> transitions;

	/**
	 * A node in the control flow graph.
	 */
	public final class Location {
		private final ProgramPoint programPoint;

		/**
		 * Creates a new location on a given program point.
		 * 
		 * @param programPoint
		 *            the program point the locations is at
		 */
		public Location(final ProgramPoint programPoint) {
			this.programPoint = programPoint;
		}

		/**
		 * Returns the program point associated with the given location.
		 * 
		 * @return program point associated with this location
		 */
		public ProgramPoint getProgramPoint() {
			return programPoint;
		}
	}

	/**
	 * An edge in the control flow graph.
	 */
	public final class Transition {
		private final TransFormula transFormula;
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
		public Transition(final TransFormula transFormula,
				final Location start, final Location end) {
			this.transFormula = transFormula;
			this.start = start;
			this.end = end;
		}

		/**
		 * Returns the {@link TransFormula} defining the behavior of the
		 * transition.
		 * 
		 * @return TransFormula defining the behvaiour of the transition
		 */
		public TransFormula getTransFormula() {
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
	}

	/**
	 * Creates a control flow graph based on given locations and transitions.
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
		final Collection<Location> innerLocations = new ArrayList<>(
				locations.size());
		innerLocations.addAll(locations);
		this.locations = Collections.unmodifiableCollection(innerLocations);
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
	 * Returns a collection of all locations within the graph. Immutable.
	 * 
	 * @return immutable collection of all locations
	 */
	public Collection<Location> getLocations() {
		return locations;
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
	 *            the location to get originating transitions for
	 * @return collection of all transitions originating in location
	 */
	public Collection<Transition> getTransitionsForLocation(
			final Location location) {
		throw new UnsupportedOperationException("not yet implemented");
	}
}
