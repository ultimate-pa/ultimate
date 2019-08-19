/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Loop Detection of the FastUPR Loop Acceleration package.
 *
 * @param <INLOC>
 *            The type of the locations of the old IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the transformed IIcfg.
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class FastUPRDetection<INLOC extends IcfgLocation> {

	private final ILogger mLogger;
	private final List<INLOC> mLoopHeads;

	/**
	 *
	 * @param logger
	 *            The {@link ILogger} used for Debug Output.
	 * @param originalIcfg
	 *            The {@link IIcfg} to be searched.
	 * @param newIcfgIdentifier
	 */
	public FastUPRDetection(final ILogger logger, final IIcfg<INLOC> originalIcfg) {
		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mLogger = Objects.requireNonNull(logger);
		mLoopHeads = getLoopHeads(origIcfg);
	}

	public List<Deque<IcfgEdge>> getLoopEdgePaths() {
		final List<Deque<IcfgEdge>> result = new ArrayList<>();
		for (final INLOC loopHead : mLoopHeads) {
			result.add(getPathEdges(loopHead));
		}
		return result;
	}

	List<Deque<INLOC>> getLoopPaths() {
		final List<Deque<INLOC>> loopPaths = new ArrayList<>();
		for (final INLOC loopHead : mLoopHeads) {
			loopPaths.add(getPathLocs(loopHead));
		}
		return loopPaths;
	}

	@SuppressWarnings("unchecked")
	private List<INLOC> getLoopHeads(final IIcfg<INLOC> originalIcfg) {

		final List<INLOC> loopHeads = new ArrayList<>();
		final Set<INLOC> init = originalIcfg.getInitialNodes();
		final Set<INLOC> closed = new HashSet<>();
		final Set<IcfgEdge> closedEdges = new HashSet<>();
		final Deque<INLOC> open = new ArrayDeque<>(init);

		while (!open.isEmpty()) {
			final INLOC currentNode = open.removeFirst();
			closed.add(currentNode);
			for (final IcfgEdge transition : currentNode.getOutgoingEdges()) {
				if (!closedEdges.add(transition)) {
					continue;
				}
				final INLOC target = (INLOC) transition.getTarget();
				mLogger.debug("Current target:" + target.toString());
				if (closed.contains(target)) {
					loopHeads.add(target);
					mLogger.debug("Loop head:" + target.toString());
				} else {
					open.addLast(target);
				}
			}
		}
		return loopHeads;
	}

	@SuppressWarnings("unchecked")
	private Deque<INLOC> getPathLocs(final INLOC loopHead) {

		final Deque<INLOC> currentPath = new ArrayDeque<>();
		final Deque<Integer> currentPathIndices = new ArrayDeque<>();

		currentPath.addLast(loopHead);
		currentPathIndices.addLast(0);

		while (!currentPath.isEmpty()) {
			if (currentPath.getLast().getOutgoingEdges().size() > currentPathIndices.getLast()) {

				final INLOC target = (INLOC) currentPath.getLast().getOutgoingEdges().get(currentPathIndices.getLast())
						.getTarget();

				final int index = currentPathIndices.removeLast();

				currentPathIndices.addLast(index + 1);
				currentPathIndices.addLast(0);
				currentPath.addLast(target);

				if (target.equals(loopHead)) {
					mLogger.debug("Found Loop Head again!");
					return currentPath;
				}
			} else {

				currentPathIndices.removeLast();
				currentPath.removeLast();
			}
		}

		return new ArrayDeque<>();
	}

	private Deque<IcfgEdge> getPathEdges(final INLOC loopHead) {
		final Map<IcfgEdge, IcfgEdge> parentMap = new HashMap<>();
		final HashSet<IcfgEdge> checked = new HashSet<>();
		final Deque<IcfgEdge> toCheck = new ArrayDeque<>();
		toCheck.addAll(loopHead.getOutgoingEdges());

		while (!toCheck.isEmpty()) {
			final IcfgEdge current = toCheck.pop();

			if (current.getTarget().equals(loopHead)) {
				return calculatePathEdges(current, parentMap);
			}

			if (!checked.add(current)) {
				continue;
			}

			for (final IcfgEdge child : current.getTarget().getOutgoingEdges()) {
				if (!current.equals(child)) {
					parentMap.put(child, current);
					toCheck.add(child);
				}
			}
		}
		return new ArrayDeque<>();
	}

	private static Deque<IcfgEdge> calculatePathEdges(IcfgEdge lastEdge, Map<IcfgEdge, IcfgEdge> parentMap) {
		final Deque<IcfgEdge> result = new ArrayDeque<>();
		final HashSet<IcfgEdge> added = new HashSet<>();
		IcfgEdge current = lastEdge;
		added.add(current);
		result.add(current);
		while (parentMap.containsKey(current)) {
			current = parentMap.get(current);
			if (!added.contains(current)) {
				result.addFirst(current);
				added.add(current);
			} else {
				return result;
			}
		}
		return result;
	}

	public List<INLOC> getLoopHeads() {
		return mLoopHeads;
	}

}
