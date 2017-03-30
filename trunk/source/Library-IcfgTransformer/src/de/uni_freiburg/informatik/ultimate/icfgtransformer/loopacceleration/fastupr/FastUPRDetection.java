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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * The main class for Fast Acceleration of Ultimately Periodic Relations
 *
 * @param <INLOC>
 *            The type of the locations of the old IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the transformed IIcfg.
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class FastUPRDetection<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> {

	private final ILogger mLogger;
	private final List<Deque<INLOC>> mLoopPaths;
	private final Map<INLOC, OUTLOC> mOldLoc2NewLoc;
	private final Map<IIcfgCallTransition<INLOC>, IcfgCallTransition> mOldCalls2NewCalls;

	public FastUPRDetection(final ILogger logger, final IIcfg<INLOC> originalIcfg, final Class<OUTLOC> outLocationClass,
			final String newIcfgIdentifier) {
		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mLogger = Objects.requireNonNull(logger);
		mOldLoc2NewLoc = new HashMap<>();
		mOldCalls2NewCalls = new HashMap<>();

		mLoopPaths = getLoops(originalIcfg);
	}

	private List<Deque<INLOC>> getLoops(final IIcfg<INLOC> originalIcfg) {
		final HashSet<INLOC> loopHeads = getLoopHeads(originalIcfg);
		final List<Deque<INLOC>> loopPaths = new ArrayList<>();
		for (final INLOC loopHead : loopHeads) {
			loopPaths.add(getPath(loopHead));
		}
		return loopPaths;
	}

	@SuppressWarnings("unchecked")
	private HashSet<INLOC> getLoopHeads(final IIcfg<INLOC> originalIcfg) {
		final HashSet<INLOC> loopHeads = new HashSet<INLOC>();
		final Set<INLOC> init = originalIcfg.getInitialNodes();
		final Set<INLOC> closed = new HashSet<>();
		final Deque<INLOC> open = new ArrayDeque<>(init);

		while (!open.isEmpty()) {
			final INLOC currentNode = open.removeFirst();
			closed.add(currentNode);
			for (final IcfgEdge transition : currentNode.getOutgoingEdges()) {
				final INLOC target = (INLOC) transition.getTarget();
				mLogger.debug("Current target:" + target.toString());
				if (closed.contains(target)) {
					loopHeads.add(target);
					mLogger.debug("Loop head:" + target.toString());
				} else {
					open.addFirst(target);
				}
			}
		}
		return loopHeads;
	}

	@SuppressWarnings({ "unused", "unchecked" })
	private Deque<INLOC> getPath(final INLOC loopHead) {

		final Deque<INLOC> currentPath = new ArrayDeque<>();
		final Deque<Integer> currentPathIndices = new ArrayDeque<>();

		currentPath.addLast(loopHead);
		currentPathIndices.addLast(0);

		while (!currentPath.isEmpty()) {
			// mLogger.debug("Outgoing Edges:");
			// mLogger.debug(currentPath.getLast().getOutgoingEdges().size());
			// mLogger.debug("Path/Indices");
			// mLogger.debug(currentPath.size());
			// mLogger.debug(currentPathIndices.size());
			if (currentPath.getLast().getOutgoingEdges().size() > currentPathIndices.getLast()) {

				final INLOC target =
						(INLOC) currentPath.getLast().getOutgoingEdges().get(currentPathIndices.getLast()).getTarget();

				// mLogger.debug("Current node: " + currentPath.getLast().toString());
				// mLogger.debug("Target node: " + target.toString());

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

		return null;
	}

	public List<Deque<INLOC>> getLoopPaths() {

		return mLoopPaths;
	}

}
