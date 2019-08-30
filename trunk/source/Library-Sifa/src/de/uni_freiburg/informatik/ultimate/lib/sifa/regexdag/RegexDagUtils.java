/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.EmptySet;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Epsilon;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Literal;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.sifa.LoopPointVisitor;

public final class RegexDagUtils {

	private RegexDagUtils() {
		// objects of this class have no purpose
	}

	/** @see #sourceLocations(RegexDag, IDagOverlay) */
	public static IcfgLocation singleSourceLocation(
			final RegexDag<IIcfgTransition<IcfgLocation>> dag,
			final IDagOverlay<IIcfgTransition<IcfgLocation>> overlay) {

		return getOnly(sinkLocations(dag, overlay));
	}

	/** @see #nextLocations(RegexDag, Collection, Function, Function) */
	public static Set<IcfgLocation> sourceLocations(
			final RegexDag<IIcfgTransition<IcfgLocation>> dag,
			final IDagOverlay<IIcfgTransition<IcfgLocation>> overlay) {

		return nextLocations(overlay.sinks(dag), IIcfgTransition::getSource, overlay::successorsOf);
	}

	/** @see #sinkLocations(RegexDag, IDagOverlay) */
	public static IcfgLocation singleSinkLocation(
			final RegexDag<IIcfgTransition<IcfgLocation>> dag,
			final IDagOverlay<IIcfgTransition<IcfgLocation>> overlay) {

		return getOnly(sinkLocations(dag, overlay));
	}

	/** @see #nextLocations(RegexDag, Collection, Function, Function) */
	public static Set<IcfgLocation> sinkLocations(
			final RegexDag<IIcfgTransition<IcfgLocation>> dag,
			final IDagOverlay<IIcfgTransition<IcfgLocation>> overlay) {

		return nextLocations(overlay.sinks(dag), IIcfgTransition::getTarget, overlay::predecessorsOf);
	}

	private static IcfgLocation getOnly(final Set<IcfgLocation> locations) {
		if (locations.size() != 1) {
			throw new IllegalArgumentException("Expected one location but found " + locations.size());
		}
		return locations.iterator().next();
	}

	/**
	 *
	 * Searches the IcfgLocations next to a given set of DAG nodes.
	 * IcfgLocation L is included if and only if there is a path …
	 * <ul>
	 * <li> starting at one of given DAG nodes
	 * <li> ending at a RegexDagNode such that node's IcfgLocation closer to the starting nodes is L ✱
	 * <li> visiting only RegexDagNodes without locations (that is, epsilon) in between
	 * </ul>
	 * <p>
	 * ✱ In the ICFG the nodes are program locations. However, in the DAG the nodes are transitions between
	 * two locations (a simple transition), one location (a loop), or no location (an epsilon node used
	 * to model forks and joins in the program flow, or an empty set regex node).
	 * The function {@code getLocationInStartPointDirection} returns the location closer to the starting nodes
	 * for cases in which there are multiple IcfgLocations per RegexDagNode.
	 *
	 * @param <T> Abbreviation for long type – this method isn't supposed to be actually generic
	 *
	 * @param startPoints Starting points for the search. Ideally no starting point can reach another
	 *                    starting point using {@code getNodesInSeachDirection}.
	 * @param getLocationInStartPointDirection See ✱
	 * @param getNodesInSeachDirection Search direction, can also be used to respect DAG overlays
	 *
	 * @return IcfgLocations corresponding to the starting nodes in search direction
	 */
	private static <T extends IIcfgTransition<IcfgLocation>> Set<IcfgLocation> nextLocations(
			final Collection<RegexDagNode<T>> startPoints,
			final Function<T, IcfgLocation> getLocationInStartPointDirection,
			final Function<RegexDagNode<T>, Collection<RegexDagNode<T>>> getNodesInSeachDirection) {

		final Set<IcfgLocation> resultLocs = new HashSet<>();

		final Queue<RegexDagNode<T>> worklist = new ArrayDeque<>();
		worklist.addAll(startPoints);

		while (!worklist.isEmpty()) {
			final RegexDagNode<T> node = worklist.remove();
			final IRegex<T> regex = node.getContent();
			if (regex instanceof Literal<?>) {
				final T icfgTransition = ((Literal<T>) regex).getLetter();
				resultLocs.add(getLocationInStartPointDirection.apply(icfgTransition));
			} else if (regex instanceof Star<?>) {
				resultLocs.add(regex.accept(new LoopPointVisitor<>()));
			} else if (regex instanceof Epsilon<?> || regex instanceof EmptySet<?>) {
				worklist.addAll(getNodesInSeachDirection.apply(node));
			} else {
				throw new AssertionError("Illegal regex type in RegexDag: " + regex);
			}
		}
		return resultLocs;
	}

}
