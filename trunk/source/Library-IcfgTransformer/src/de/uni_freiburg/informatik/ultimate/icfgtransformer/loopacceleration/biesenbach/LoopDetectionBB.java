/*
 * Copyright (C) 2017 Ben Biesenbach (Ben.Biesenbach@gmx.de)
 * Copyright (C) 2016-2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Extracts the loops from an {@link IIcfg}.
 *
 * @param <INLOC>
 *            The type of the locations of the IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the IIcfg with only loops left.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Ben Biesenbach (Ben.Biesenbach@gmx.de)
 */
public class LoopDetectionBB<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final ILogger mLogger;
	private final BasicIcfg<OUTLOC> mResultIcfg;

	/**
	 * Extracts the loops from an {@link IIcfg}.
	 * 
	 * @param logger
	 * @param originalIcfg
	 * @param outLocationClass
	 * @param funLocFac
	 * @param newIcfgIdentifier
	 * @param transformer
	 * @param backtranslationTracker
	 */
	public LoopDetectionBB(final ILogger logger, final IIcfg<INLOC> originalIcfg, final Class<OUTLOC> outLocationClass,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final String newIcfgIdentifier,
			final ITransformulaTransformer transformer, final IBacktranslationTracker backtranslationTracker) {
		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mLogger = Objects.requireNonNull(logger);
		final BasicIcfg<OUTLOC> result =
				new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
		transformer.preprocessIcfg(origIcfg);
		final TransformedIcfgBuilder<INLOC, OUTLOC> lst =
				new TransformedIcfgBuilder<>(funLocFac, backtranslationTracker, transformer, origIcfg, result);
		// perform transformation last
		getLoop(origIcfg, result, lst);
		lst.finish();
		mResultIcfg = result;
	}

	/*
	 * ---------second attempt---------- (extracts the loops of a program)
	 */

	private void getLoop(final IIcfg<INLOC> origIcfg, final BasicIcfg<OUTLOC> resultIcfg,
			final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {
		for (final INLOC loopHead : origIcfg.getLoopLocations()) {
			final Deque<INLOC> path = new ArrayDeque<>();
			path.addLast(loopHead);
			transformPathToIcfg(origIcfg, resultIcfg, getLoopPath(path), lst);
		}
	}

	@SuppressWarnings("unchecked")
	private Deque<INLOC> getLoopPath(final Deque<INLOC> path) {
		Deque<INLOC> loopPath = null;
		for (final IcfgEdge transition : path.getLast().getOutgoingEdges()) {
			if (transition.getTarget().equals(path.getFirst())) {
				path.addLast((INLOC) transition.getTarget());
				return path;
			}
			final Deque<INLOC> newPath = new ArrayDeque<>(path);
			newPath.addLast((INLOC) transition.getTarget());
			final Deque<INLOC> returnedPath = getLoopPath(newPath);
			if (returnedPath != null) {
				loopPath = returnedPath;
			}
		}
		return loopPath;
	}

	@SuppressWarnings("unchecked")
	private void transformPathToIcfg(final IIcfg<INLOC> origIcfg, final BasicIcfg<OUTLOC> resultIcfg,
			final Deque<INLOC> path, final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {

		final Set<INLOC> init = origIcfg.getInitialNodes();
		final Deque<INLOC> open = new ArrayDeque<>(init);
		final Set<INLOC> closed = new HashSet<>();

		// Connect initial nodes with loopHead
		final INLOC oldMainENTRY = open.removeFirst();
		closed.add(oldMainENTRY);
		final OUTLOC newMainENTRY = lst.createNewLocation(oldMainENTRY);
		final OUTLOC newLoopHead = lst.createNewLocation(path.getFirst());
		// TODO Which transition is needed? Or is there even a way without mainENTRY?
		// DD: Assume that there is only one initial node. If there are more, throw an exception.
		final IcfgEdge newTransitionLH = new IcfgInternalTransition(newMainENTRY, newLoopHead, null, null);
		newMainENTRY.addOutgoing(newTransitionLH);
		newLoopHead.addIncoming(newTransitionLH);
		open.add(path.getFirst());
		path.removeFirst();

		// Add the loopBody to the Icfg
		while (!open.isEmpty()) {
			final INLOC oldSource = open.removeFirst();
			if (!closed.add(oldSource)) {
				continue;
			}

			final OUTLOC newSource = lst.createNewLocation(oldSource);
			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
				final INLOC oldTarget;
				// Check if transition is part of the path
				if (oldTransition.getTarget().equals(path.getFirst())) {
					oldTarget = (INLOC) oldTransition.getTarget();
				} else {
					// TODO Which transition is needed for the exit? If there are multiple exits, which are the right
					// ones?
					// DD: Each procedure has one distinct exit node. But this is not necessarily the end of the
					// program. The Icfg itself has no "exit" node.
					oldTarget = origIcfg.getProcedureExitNodes().values().iterator().next();
				}
				open.add(oldTarget);
				final OUTLOC newTarget = lst.createNewLocation(oldTarget);
				lst.createNewTransition(newSource, newTarget, oldTransition);
			}
			if (!path.isEmpty()) {
				path.removeFirst();
			}
		}
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}

	/*
	 * ----------first attempt---------- (only checks if program has a loop)
	 * 
	 * public boolean isLooped(final IIcfg<INLOC> originalIcfg) { final Set<INLOC> init =
	 * originalIcfg.getInitialNodes(); final Deque<INLOC> queue = new ArrayDeque<>(init); final Deque<INLOC> marked =
	 * new ArrayDeque<>();
	 * 
	 * while (!queue.isEmpty()) { final INLOC node = queue.removeFirst(); if(recursivHelper(node, marked)){ return true;
	 * } } return false; }
	 * 
	 * @SuppressWarnings("unchecked") private boolean recursivHelper(INLOC node, Deque<INLOC> marked){ if
	 * (marked.contains(node)) { return true; } marked.add(node); for (final IcfgEdge transition :
	 * node.getOutgoingEdges()) { if(recursivHelper((INLOC) transition.getTarget(), new ArrayDeque<>(marked))){ return
	 * true; } } return false; }
	 */
}