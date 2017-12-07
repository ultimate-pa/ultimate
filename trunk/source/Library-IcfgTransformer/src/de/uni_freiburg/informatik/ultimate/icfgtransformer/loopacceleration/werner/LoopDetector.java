/*
 * Copyright (C) 2017 Jonas Werner (jonaswerner95@gmail.com)
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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Extracts the loops from an {@link IIcfg}. And calculates its backbones, which
 * are acyclic paths in the loop.
 *
 * @param <INLOC>
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 */

public class LoopDetector<INLOC extends IcfgLocation> {
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private Map<IcfgLocation, Loop> mLoopBodies;
	private final IUltimateServiceProvider mServices;
	private final Set<INLOC> mErrorLocations;
	private final Set<INLOC> mLoopHeads;
	private final Set<IcfgLocation> mIllegalLoopHeads;
	private final Map<IcfgLocation, Loop> mNestedLoopHierachy;

	private final Map<IcfgLocation, IcfgLocation> mNesting;
	private final Map<IcfgLocation, IcfgLocation> mNested;
	private final Map<IcfgLocation, Set<IcfgEdge>> mLoopExitTransitions;
	private final Map<IcfgLocation, IcfgLocation> mLoopExitNodes;

	private final int mBackboneLimit;

	/**
	 * Loop Detector for retrieving loops in an {@link IIcfg}.
	 *
	 * @param logger
	 * @param originalIcfg
	 * @param services
	 * @param script
	 */
	public LoopDetector(final ILogger logger, final IIcfg<INLOC> originalIcfg, final ManagedScript script,
			final IUltimateServiceProvider services, final int backboneLimit) {
		mLogger = Objects.requireNonNull(logger);
		mServices = services;
		mScript = script;
		mErrorLocations = IcfgUtils.getErrorLocations(originalIcfg);
		mLoopHeads = originalIcfg.getLoopLocations();
		mIllegalLoopHeads = new HashSet<>();
		mNestedLoopHierachy = new HashMap<>();
		mNesting = new HashMap<>();
		mNested = new HashMap<>();
		mLoopBodies = new HashMap<>();
		mLoopExitTransitions = new HashMap<>();
		mLoopExitNodes = new HashMap<>();

		mBackboneLimit = backboneLimit;

		final Set<INLOC> initialNodes = originalIcfg.getInitialNodes();

		if (initialNodes.size() > 1) {
			return;
		}
		
		getLoop();

		for (Entry<IcfgLocation, Loop> entry : mLoopBodies.entrySet()) {

			final Loop loop = entry.getValue();
			final Deque<Backbone> backbones = getBackbonePath(loop);

			UnmodifiableTransFormula loopFormula = (UnmodifiableTransFormula) backbones.getFirst().getFormula();

			for (final Backbone backbone : backbones) {
				mLogger.debug("Backbone " + backbone);
				loopFormula = TransFormulaUtils.parallelComposition(mLogger, mServices, 0, mScript, null, false,
						XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, loopFormula,
						(UnmodifiableTransFormula) backbone.getFormula());
				loop.addBackbone(backbone);
			}
			loop.setFormula(loopFormula);
			loop.setInVars(loopFormula.getInVars());
			loop.setOutVars(loopFormula.getOutVars());

			if (mNestedLoopHierachy.containsKey(entry.getKey())) {
				mNestedLoopHierachy.get(entry.getKey()).setNested();
				mNestedLoopHierachy.get(entry.getKey()).addNestedLoop(loop);
			}
		}
		mLogger.debug("Loop detector done.");
	}

	/**
	 * Get Loops of the originalIcfg.
	 * 
	 * @param originalIcfg
	 * @return
	 */
	private void getLoop() {

		if (!mLoopHeads.isEmpty()) {
			mLogger.debug("Loops found.");

			for (final IcfgLocation loopHead : mLoopHeads) {
				if (mIllegalLoopHeads.contains(loopHead)) {
					continue;
				}
				final Loop loop = new Loop(loopHead, mScript);
				final Deque<IcfgEdge> path = getPath(loopHead, loop, loopHead, Collections.emptySet());
				loop.setPath(path);

				if (loop.getPath().isEmpty()) {
					continue;
				}

				// Assuming there is only one loopexitnode
				for (IcfgEdge edge : loopHead.getOutgoingEdges()) {
					if (!loop.getPath().contains(edge)) {
						mLogger.debug("found LoopExit");
						loop.setLoopExit(edge.getTarget());
					}
				}

				mLoopBodies.put(loopHead, loop);
			}

		} else {
			mLogger.debug("No Loops found.");
		}
	}

	private Deque<IcfgEdge> getPath(final IcfgLocation start, final Loop loop, final IcfgLocation target,
			final Set<IcfgEdge> forbiddenEdgeSet) {
		
		Deque<IcfgEdge> loopPath = new ArrayDeque<>();
		final Deque<IcfgEdge> stack = new ArrayDeque<>();
		stack.addAll(start.getOutgoingEdges());

		while (!stack.isEmpty()) {
			final IcfgEdge edge = stack.pop();
			final IcfgLocation node = edge.getTarget();

			final Deque<IcfgEdge> newPath = new ArrayDeque<>(loopPath);
			newPath.addLast(edge);

			if (mErrorLocations.contains(node)) {
				mLogger.debug("FOUND ERROR LOCATIONS");
				mErrorLocations.remove(edge.getTarget());
				final Deque<IcfgEdge> errorPath = getPath(start, loop, edge.getTarget(), Collections.emptySet());
				final TransFormula errorFormula = calculateFormula(errorPath);
				final Backbone errorLocationPath = new Backbone(errorPath, errorFormula, false,
						Collections.emptyList());
				loop.addErrorPath(edge.getTarget(), errorLocationPath);
			}

			if (!findLoopHeader(newPath, start, target, Collections.emptySet(), Collections.emptySet(), false)
					|| forbiddenEdgeSet.contains(edge)) {
				continue;
			}

			if (mLoopHeads.contains(node) && !node.equals(start) && !node.equals(target)) {
				if ((mNested.containsKey(start) && mNested.get(start).equals(node))
						|| mNestedLoopHierachy.containsKey(node)) {
					continue;
				}
				mLogger.debug("FOUND NESTED LOOPHEAD: " + edge.getTarget());
				mNestedLoopHierachy.put(edge.getTarget(), loop);

				final Deque<IcfgEdge> nestedPath = new ArrayDeque<>(newPath);

				for (final IcfgEdge nestedExit : mLoopExitTransitions.get(node)) {
					nestedPath.addLast(nestedExit);
					if (findLoopHeader(nestedPath, start, target, Collections.emptySet(), Collections.emptySet(),
							false)) {
						loopPath = nestedPath;
					}
					if (!nestedExit.getTarget().equals(target)) {
						stack.addAll(nestedExit.getTarget().getOutgoingEdges());
					}
				}
				continue;
			}

			loopPath = newPath;
			if (!edge.getTarget().equals(target)) {
				stack.addAll(node.getOutgoingEdges());
			}

		}
		return loopPath;

	}

	/**
	 * Try to find a path back to the loopheader. If there is one return true,
	 * else false.
	 *
	 * @param path
	 *            path to check
	 * @param start
	 *            starting node
	 *
	 * @param target
	 *            target node
	 * 
	 * @param forbidden
	 *            edges which are forbidden which means they are not allowed to
	 *            turn up in searching of the target
	 * @param forbiddenNode
	 *            nodes that are forbidden which means they are not allowed to
	 *            turn up in searching of the target
	 * @param plain
	 *            select if one wants to check for nested loops or just try to
	 *            find the target
	 */
	private boolean findLoopHeader(final Deque<IcfgEdge> path, final IcfgLocation start, final IcfgLocation target,
			Set<IcfgEdge> forbidden, Set<IcfgLocation> forbiddenNode, final boolean plain) {

		final Set<IcfgEdge> forbiddenEdges = new HashSet<>(forbidden);
		final Set<IcfgLocation> forbiddenNodes = new HashSet<>(forbiddenNode);
		final Set<IcfgLocation> newHeads = new HashSet<>(mLoopHeads);
		final Deque<IcfgEdge> stack = new ArrayDeque<>();
		final Deque<IcfgLocation> visited = new ArrayDeque<>();
		stack.push(path.getLast());
		newHeads.remove(target);
		newHeads.removeAll(mIllegalLoopHeads);

		while (!stack.isEmpty()) {

			final IcfgEdge edge = stack.pop();
			final IcfgLocation node = edge.getTarget();

			if (node.equals(target)) {
				return true;
			}

			if (visited.contains(node) || forbiddenEdges.contains(edge) || forbiddenNodes.contains(node)
					|| node.equals(start)) {
				continue;
			}

			if (newHeads.contains(node) && !plain) {
				if (mNested.containsKey(start)) {
					continue;
				}
				if (mNesting.containsKey(start) && mNesting.get(start).equals(node)) {
					return true;
				}
				if (!mNested.containsKey(start) && !mNesting.containsKey(node)) {
					checkNesting(start, node);
					stack.add(edge);
					continue;
				}
			}

			visited.addLast(node);
			stack.addAll(node.getOutgoingEdges());

		}
		return false;
	}

	/**
	 * 
	 * 
	 * check who is nested in whom
	 * 
	 * 
	 */
	private void checkNesting(final IcfgLocation start, final IcfgLocation node) {
		if (mNested.containsKey(start) || (mNesting.containsKey(start) && mNesting.get(start).equals(node))) {
			return;
		}

		for (final IcfgEdge transition : node.getOutgoingEdges()) {
			final Deque<IcfgEdge> path = new ArrayDeque<>();
			path.addLast(transition);
			if (findLoopHeader(path, node, node, Collections.emptySet(), Collections.emptySet(), true)) {
				break;
			}
			mIllegalLoopHeads.add(node);
			return;
		}

		final Set<IcfgLocation> forbidden = new HashSet<>();
		forbidden.add(node);

		// if there is one edge that does not go to the loophead
		for (final IcfgEdge exit : start.getOutgoingEdges()) {
			final Deque<IcfgEdge> path = new ArrayDeque<>();
			path.addLast(exit);

			if (findLoopHeader(path, start, start, Collections.emptySet(), forbidden, false)) {
				mNested.put(start, node);
				mNesting.put(node, start);
				findLoopExits(node, start);
				return;
			}
		}
		mNested.put(node, start);
		mNesting.put(start, node);
		findLoopExits(start, node);
		return;
	}

	/**
	 * Find the exittransitions of a loop, needed for nestedloops
	 * 
	 * @param nestingHead
	 * @param loopHead
	 */
	private void findLoopExits(final IcfgLocation nestingHead, final IcfgLocation loopHead) {
		final Set<IcfgLocation> forbiddenNodes = new HashSet<>();
		forbiddenNodes.add(nestingHead);

		for (final IcfgEdge exit : loopHead.getOutgoingEdges()) {
			final Deque<IcfgEdge> path = new ArrayDeque<>();
			path.addLast(exit);

			if (!findLoopHeader(path, loopHead, loopHead, Collections.emptySet(), forbiddenNodes, false)) {
				final Set<IcfgEdge> oldExits = new HashSet<>();
				oldExits.add(exit);
				mLoopExitTransitions.put(loopHead, oldExits);
				mLoopExitNodes.put(loopHead, exit.getTarget());

				/**
				 * when a loop has multiple exittransitions that do not start on
				 * the loopheader
				 */
				for (final IcfgEdge trans : exit.getTarget().getIncomingEdges()) {
					final IcfgLocation source = trans.getSource();
					for (final IcfgEdge out : source.getOutgoingEdges()) {
						final Deque<IcfgEdge> exitPath = new ArrayDeque<>();
						exitPath.addLast(out);
						if (findLoopHeader(exitPath, source, loopHead, Collections.emptySet(), forbiddenNodes, false)) {
							final Set<IcfgEdge> oldExit = new HashSet<>(mLoopExitTransitions.get(loopHead));
							oldExit.add(trans);
							mLoopExitTransitions.put(loopHead, oldExit);
							continue;
						}
					}

				}

			}

		}

	}

	/**
	 * Get the backbone paths of a given loop
	 * 
	 * @param loop
	 * @return
	 */
	private Deque<Backbone> getBackbonePath(final Loop loop) {
		final Deque<IcfgEdge> loopBody = loop.getPath();
		final Deque<Backbone> backbones = new ArrayDeque<>();
		final IcfgLocation loopHead = loopBody.getFirst().getSource();
		final IcfgEdge initialEdge = loopBody.getFirst();
		final Deque<Deque<IcfgEdge>> possibleBackbones = new ArrayDeque<>();
		final Deque<IcfgEdge> first = new ArrayDeque<>();

		first.addLast(initialEdge);
		possibleBackbones.addFirst(first);

		while (!possibleBackbones.isEmpty()) {
			final Deque<IcfgLocation> visited = new ArrayDeque<>();
			final Deque<IcfgEdge> backbone = possibleBackbones.pop();
			final ArrayList<Loop> nestedLoops = new ArrayList<>();
			Boolean nested = false;
			Boolean looped = false;

			while (!backbone.getLast().getTarget().equals(loopHead)) {

				final IcfgLocation target = backbone.getLast().getTarget();

				if (target.equals(loop.getLoopExit())) {
					
					final Set<IcfgEdge> forbidden = new HashSet<>(loop.getExitTransitions());
					forbidden.addAll(loop.getBreakPaths());
					forbidden.remove(backbone.getLast());
					final Deque<IcfgEdge> breakPath = getPath(loop.getLoophead(), loop, target, forbidden);
					final TransFormula errorFormula = calculateFormula(breakPath);
					loop.addBreakFormula((UnmodifiableTransFormula) errorFormula);
					loop.addBreakPath(backbone.getLast());
					looped = true;
					break;
				}

				if (visited.contains(target)) {
					looped = true;
					break;
				}

				visited.addLast(target);

				/**
				 * When we find a nested loophead we continue using its
				 * exittransitions for the backbones.
				 */
				if (mNesting.containsKey(loopHead) && mNesting.get(loopHead).equals(target)) {
					for (int i = 1; i < mLoopBodies.get(target).getExitTransitions().size(); i++) {
						final Deque<IcfgEdge> newPossibleBackbone = new ArrayDeque<>(backbone);
						newPossibleBackbone.addLast(mLoopBodies.get(target).getExitTransitions().get(i));
						possibleBackbones.addLast(newPossibleBackbone);
					}
					backbone.add(mLoopBodies.get(target).getExitTransitions().get(0));
					continue;
				}

				/**
				 * in case of multiple outgoing edges create more possible
				 * backbones.
				 */
				if (!target.getOutgoingEdges().isEmpty()) {
					for (int i = 1; i < target.getOutgoingEdges().size(); i++) {
						final Deque<IcfgEdge> newPossibleBackbone = new ArrayDeque<>(backbone);
						newPossibleBackbone.addLast(target.getOutgoingEdges().get(i));
						possibleBackbones.addLast(newPossibleBackbone);
					}
					backbone.add(target.getOutgoingEdges().get(0));
				}
			}

			if (looped) {
				continue;
			}

			/**
			 * Mark backbones that contain a nested loopHead as nested for
			 * later.
			 */
			for (final IcfgEdge edge : backbone) {
				final IcfgLocation target = edge.getTarget();
				if (mNestedLoopHierachy.containsKey(target) && !target.equals(loopHead)) {
					nestedLoops.add(mLoopBodies.get(target));
					nested = true;
				}
			}
			final TransFormula tf = calculateFormula(backbone);
			final Backbone newBackbone = new Backbone(backbone, tf, nested, nestedLoops);

			mLogger.debug("found Backbone " + newBackbone);

			/**
			 * Limiting the number of backbones.
			 */
			if (backbones.size() > mBackboneLimit) {
				mLogger.warn("Found more backbones than the limit allows...");
			}
			backbones.addLast(newBackbone);
		}
		return backbones;
	}

	/**
	 * Calculate a backbones {@link TransFormula}
	 * 
	 * @param path
	 * @return
	 */
	private TransFormula calculateFormula(final Deque<IcfgEdge> path) {
		final List<UnmodifiableTransFormula> transformulas = new ArrayList<>();

		for (final IcfgEdge edge : path) {
			transformulas.add(edge.getTransformula());
		}

		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mScript, true, true, false,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, SimplificationTechnique.NONE,
				transformulas);
	}

	/**
	 * Get Loop bodies of an {@link IIcfg}. As a Queue of loop datastructures
	 */
	public Map<IcfgLocation, Loop> getLoopBodies() {
		return mLoopBodies;
	}
}
