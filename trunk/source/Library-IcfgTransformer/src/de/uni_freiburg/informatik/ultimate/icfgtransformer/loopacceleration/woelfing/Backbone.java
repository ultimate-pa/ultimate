/*
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.woelfing;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * A Backbone.
 *
 * @author Dennis Wölfing
 *
 */
public class Backbone {
	private final List<IcfgEdge> mTransitions;

	/**
	 * Constructs a Backbone with an initial transition.
	 *
	 * @param transition
	 *            The entry transition of the Backbone.
	 */
	public Backbone(final IcfgEdge transition) {
		mTransitions = new ArrayList<>();
		mTransitions.add(transition);
	}

	/**
	 * Constructs a copy of a Backbone.
	 *
	 * @param other
	 *            The original Backbone.
	 */
	public Backbone(final Backbone other) {
		mTransitions = new ArrayList<>(other.mTransitions);
	}

	/**
	 * Appends a transition to the Backbone.
	 *
	 * @param transition
	 *            The transition to append.
	 */
	public void addTransition(final IcfgEdge transition) {
		mTransitions.add(transition);
	}

	/**
	 * Checks whether the Backbone contains the given location.
	 *
	 * @param location
	 *            An IcfgLocation.
	 * @return true if the Backbone contains the location.
	 */
	public boolean containsLocation(final IcfgLocation location) {
		for (final IcfgEdge transition : mTransitions) {
			if (transition.getSource().equals(location)) {
				return true;
			}
		}
		return getLastLocation().equals(location);
	}

	/**
	 * Checks whether the Backbone ends in a loop.
	 *
	 * @return true if the Backbone end in a loop.
	 */
	public boolean endsInLoop() {
		final IcfgLocation lastLocation = getLastLocation();
		for (final IcfgEdge edge : mTransitions) {
			if (edge.getSource().equals(lastLocation)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Gets the last location of the Backbone.
	 *
	 * @return An IcfgLocation.
	 */
	public IcfgLocation getLastLocation() {
		return mTransitions.get(mTransitions.size() - 1).getTarget();
	}

	/**
	 * Gets the transition that enters the loop.
	 *
	 * @return The transition that enters the loop or null if the Backbone does not end in a loop.
	 */
	public IcfgEdge getLoopEntryTransition() {
		final IcfgLocation loopEntry = getLastLocation();

		for (final IcfgEdge edge : mTransitions) {
			if (edge.getSource().equals(loopEntry)) {
				return edge;
			}
		}

		return null;
	}

	public List<IcfgEdge> getTransitions() {
		return mTransitions;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("[");
		for (final IcfgEdge edge : mTransitions) {
			builder.append(edge.getSource());
			builder.append(", ");
		}
		builder.append(getLastLocation());
		builder.append("]");
		return builder.toString();
	}
}
