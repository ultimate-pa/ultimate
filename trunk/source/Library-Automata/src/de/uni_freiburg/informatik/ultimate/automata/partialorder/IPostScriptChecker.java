/*
 * Copyright (C) 2021 Dennis Wölfing
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;

/**
 * An interface that supports identifying post-scripts of a certain language.
 *
 * A set of transitions T of a Petri net N is called a post-script of a language L iff for all firing sequences sigma of
 * N, it holds that if for all t in T such that sigma.t is a firing sequence, label(sigma.t) is in L, then simply
 * label(sigma) is already in L.
 *
 * In other words, firing a transition in T cannot make a non-accepted prefix into an accepted word.
 *
 * For an example, consider {@link InfeasPostScriptChecker}.
 *
 * @param <L>
 *            The type of the letters in the Petri net.
 * @param <P>
 *            The type of the places in the Petri net.
 */
public interface IPostScriptChecker<L, P> {
	/**
	 * Checks whether execution might get stuck at the given place. This is the case if there exists a valuation for
	 * which none of the successor transitions' formulas is satisfied. This function will return true if this property
	 * cannot be proven. Note that predecessor locations of the transitions are not taken into account. They are assumed
	 * to be not more restrictive than the formulas. This function may cache the result.
	 *
	 * @param petriNet
	 *            The Petri net.
	 * @param place
	 *            A place in the Petri net.
	 * @return false if there is always successor transition with a satisfied formula, true if there might not be one.
	 *
	 * @deprecated Use {@link #isPostScript(IPetriNet, Set)} as soon as caching is sorted out
	 */
	@Deprecated(since = "2021-09-13")
	default boolean mightGetStuck(final IPetriNet<L, P> petriNet, final P place) {
		return !isPostScript(petriNet, petriNet.getSuccessors(place));
	}

	/**
	 * Determines if a given set of transitions is a post-script for the language L of this instance.
	 *
	 * @param net
	 *            The underlying Petri net
	 * @param transitions
	 *            The set of transitions that might be a post-script
	 * @return true if the set is guaranteed to be a post-script; false if it is not a post-script, or the answer could
	 *         not be determined.
	 */
	boolean isPostScript(final IPetriNet<L, P> net, final Set<Transition<L, P>> transitions);
}
