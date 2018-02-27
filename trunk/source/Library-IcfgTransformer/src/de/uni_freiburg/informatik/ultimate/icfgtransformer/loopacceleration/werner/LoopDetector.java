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
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Extracts the loops from an {@link IIcfg}. And calculates its backbones, which are acyclic paths in the loop.
 *
 * @param <INLOC>
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 */

public class LoopDetector<INLOC extends IcfgLocation> {
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final Map<IcfgLocation, Loop> mLoopBodies;
	private final IUltimateServiceProvider mServices;
	private final Set<INLOC> mErrorLocations;
	private final Set<INLOC> mLoopHeads;
	private final Set<IcfgLocation> mIllegalLoopHeads;

	private final Map<IcfgLocation, IcfgLocation> mNesting;
	private final Map<IcfgLocation, IcfgLocation> mNested;
	private final Map<IcfgLocation, IcfgLocation> mLoopExitNodes;

	private final HashMap<IcfgLocation, Deque<Backbone>> mBackbones;

	private final int mBackboneLimit;

	/**
	 * Loopdetector for finding feasible loops in an Icfg.
	 *
	 * @param logger
	 *            {@link ILogger}
	 * @param originalIcfg
	 *            {@link IIcfg}
	 * @param loopHeads
	 *            a set of loopentry locations
	 * @param script
	 *            {@link ManagedScript}
	 * @param services
	 *            {@link IUltimateServiceProvider}
	 * @param backboneLimit
	 *            a limit for number of backbones. Send notification if there are more backbones than the limit.
	 */
	public LoopDetector(final ILogger logger, final IIcfg<INLOC> originalIcfg, final Set<INLOC> loopHeads,
			final ManagedScript script, final IUltimateServiceProvider services, final int backboneLimit) {
		mLogger = Objects.requireNonNull(logger);
		mServices = services;
		mScript = script;
		mErrorLocations = IcfgUtils.getErrorLocations(originalIcfg);
		mLoopHeads = loopHeads;
		mIllegalLoopHeads = new HashSet<>();
		mNesting = new HashMap<>();
		mNested = new HashMap<>();
		mLoopBodies = new HashMap<>();
		mLoopExitNodes = new HashMap<>();

		mBackbones = new HashMap<>();

		mBackboneLimit = backboneLimit;

		for (final IcfgLocation loopHead : mLoopHeads) {
			final Loop loop = new Loop(loopHead, mScript);
			mLoopBodies.put(loopHead, loop);
		}

		/**
		 * find loops.
		 */
		getLoop();

		mLogger.debug("Found Backbones: " + mBackbones);
		if (mBackbones.size() > mBackboneLimit) {
			mLogger.warn("Found more backbones than the limit allows... This might take a while.");
		}
		mLogger.debug("Loop detector done." + System.lineSeparator());
	}

	/**
	 * Get Loops of the originalIcfg.
	 *
	 * @param originalIcfg
	 * @return
	 */
	private void getLoop() {

		for (final IcfgLocation loopHead : mLoopHeads) {
			/**
			 * first initialize the loops and get the backbones for each loop.
			 */
			mLogger.debug("LoopHead: " + loopHead);
			final Deque<Backbone> backbones = getBackbonePath(mLoopBodies.get(loopHead));
			mBackbones.put(loopHead, backbones);
		}

		/**
		 * check backbones for nested loops and sort out backbones that are nested in eachother.
		 */
		checkBackbones();

		for (final Loop loop : mLoopBodies.values()) {
			final IcfgLocation loopHead = loop.getLoophead();

			/**
			 * if the loop does not have an exit yet.
			 */
			if (!mLoopExitNodes.containsKey(loopHead)) {
				final Set<IcfgLocation> forbidden = new HashSet<>();
				forbidden.add(loopHead);
				findLoopExits(loopHead, forbidden);
			}

			/**
			 * Remove loops that do not have backbones, or where no loopexits could be found.
			 */
			if (mIllegalLoopHeads.contains(loopHead) || mBackbones.get(loopHead).isEmpty()
					|| !mLoopExitNodes.containsKey(loopHead)) {
				mLoopBodies.remove(loopHead);
				continue;
			}
			final Deque<Backbone> backbones = mBackbones.get(loop.getLoophead());

			/**
			 * Assign the properties, loopexit, backbones, looppath, loopformula to the loops.
			 */
			loop.setBackbones(backbones);
			final Pair<UnmodifiableTransFormula, Set<IcfgEdge>> path = mergeBackbones(backbones);
			loop.setFormula(path.getFirst());
			loop.setPath(path.getSecond());
			loop.setInVars(path.getFirst().getInVars());
			loop.setOutVars(path.getFirst().getOutVars());

			loop.setLoopExit(mLoopExitNodes.get(loopHead));

		}
	}

	/**
	 * Check backbones for nested loops and remove backbones that are nested in each other.
	 */
	private void checkBackbones() {
		final Deque<Backbone> backbones = new ArrayDeque<>();
		for (final Deque<Backbone> bone : mBackbones.values()) {
			backbones.addAll(bone);
		}

		for (final Backbone backbone1 : backbones) {

			final IcfgLocation loopHead1 = backbone1.getNodes().getFirst();

			for (final Backbone backbone2 : backbones) {
				final IcfgLocation loopHead2 = backbone2.getNodes().getFirst();
				if (loopHead1.equals(loopHead2)) {
					continue;
				}
				if (backbone1.getNodes().contains(loopHead2) && backbone2.getNodes().contains(loopHead1)) {

					/**
					 * remove loops that are looped in eachother, not nested. (i.e., loops that traverse call/return)
					 */
					if (mIllegalLoopHeads.contains(loopHead1)) {
						mIllegalLoopHeads.add(loopHead2);
						continue;
					}

					if (mIllegalLoopHeads.contains(loopHead2)) {
						mIllegalLoopHeads.add(loopHead1);
						continue;
					}

					/**
					 * check which loop is nested in which.
					 */
					checkNesting(loopHead1, loopHead2);

					if (mNested.containsKey(loopHead2) && mNested.get(loopHead2).equals(loopHead1)) {
						mBackbones.get(loopHead2).remove(backbone2);
						backbone1.addNestedLoop(loopHead2);
						mLoopBodies.get(loopHead1).addNestedLoop(mLoopBodies.get(loopHead2));
						continue;
					}

					if (mNested.containsKey(loopHead1) && mNested.get(loopHead1).equals(loopHead2)) {
						mBackbones.get(loopHead1).remove(backbone1);
						backbone1.addNestedLoop(loopHead1);
						mLoopBodies.get(loopHead2).addNestedLoop(mLoopBodies.get(loopHead1));
						continue;
					}

					mIllegalLoopHeads.add(backbone1.getNodes().getFirst());
					mIllegalLoopHeads.add(backbone2.getNodes().getFirst());
				}
			}
		}

		for (final IcfgLocation forbidden : mIllegalLoopHeads) {
			mBackbones.remove(forbidden);
			mLoopBodies.remove(forbidden);
		}
		mLogger.debug("Backbones checked.");
	}

	/**
	 * Try to find a path back to the loopheader. If there is one return true, else false.
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
	 *            edges which are forbidden which means they are not allowed to turn up in searching of the target
	 * @param forbiddenNode
	 *            nodes that are forbidden which means they are not allowed to turn up in searching of the target
	 * @param plain
	 *            select if one wants to check for nested loops or just try to find the target
	 */
	private boolean findLoopHeader(final IcfgEdge transition, final IcfgLocation start, final IcfgLocation target,
			final Set<IcfgEdge> forbidden, final Set<IcfgLocation> forbiddenNode, final boolean plain) {

		final Set<IcfgEdge> forbiddenEdges = new HashSet<>(forbidden);
		final Set<IcfgLocation> forbiddenNodes = new HashSet<>(forbiddenNode);
		final Set<IcfgLocation> newHeads = new HashSet<>(mLoopHeads);
		final Deque<IcfgEdge> stack = new ArrayDeque<>();
		final Deque<IcfgLocation> visited = new ArrayDeque<>();
		stack.push(transition);
		newHeads.remove(target);
		newHeads.removeAll(mIllegalLoopHeads);

		visited.addLast(start);

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
				if (mLoopExitNodes.containsKey(node)) {
					stack.addAll(mLoopBodies.get(node).getExitTransitions());
				} else {
					forbiddenNodes.add(start);
					findLoopExits(node, forbiddenNodes);
				}
			}
			visited.addLast(node);
			stack.addAll(node.getOutgoingEdges());
		}
		return false;
	}

	/**
	 * Try to find a path back to the loopheader. If there is one return true, else false.
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
	 *            edges which are forbidden which means they are not allowed to turn up in searching of the target
	 * @param forbiddenNode
	 *            nodes that are forbidden which means they are not allowed to turn up in searching of the target
	 * @param plain
	 *            select if one wants to check for nested loops or just try to find the target
	 */
	private boolean findLoopHeader(final Deque<IcfgEdge> transition, final IcfgLocation start,
			final IcfgLocation target, final Set<IcfgEdge> forbidden, final Set<IcfgLocation> forbiddenNode,
			final boolean plain) {

		final Set<IcfgEdge> forbiddenEdges = new HashSet<>(forbidden);
		final Set<IcfgLocation> forbiddenNodes = new HashSet<>(forbiddenNode);
		final Set<IcfgLocation> newHeads = new HashSet<>(mLoopHeads);
		final Deque<IcfgEdge> stack = new ArrayDeque<>();
		final Deque<IcfgLocation> visited = new ArrayDeque<>();
		stack.addAll(transition);
		newHeads.remove(target);
		newHeads.removeAll(mIllegalLoopHeads);

		visited.addLast(start);

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
				if (mLoopExitNodes.containsKey(node)) {
					stack.addAll(mLoopBodies.get(node).getExitTransitions());
				} else {
					forbiddenNodes.add(start);
					findLoopExits(node, forbiddenNodes);
				}
			}
			visited.addLast(node);
			stack.addAll(node.getOutgoingEdges());
		}
		return false;
	}

	/**
	 * check who is nested in whom
	 */
	private void checkNesting(final IcfgLocation loopHead1, final IcfgLocation loopHead2) {
		if ((mNested.containsKey(loopHead1) && mNested.get(loopHead1).equals(loopHead2))
				|| (mNesting.containsKey(loopHead1) && mNesting.get(loopHead1).equals(loopHead2))) {
			return;
		}

		final Set<IcfgLocation> forbidden = new HashSet<>();
		forbidden.add(loopHead2);
		forbidden.add(loopHead1);

		final Deque<IcfgEdge> loopHead1Edges = new ArrayDeque<>(loopHead1.getOutgoingEdges());
		if (mNested.containsKey(loopHead1)) {
			forbidden.add(mNested.get(loopHead1));
		}
		/**
		 * If it is not possible to reach one loophead without going over the other, the first one is nested in the
		 * other.
		 */
		if (!findLoopHeader(loopHead1Edges, loopHead1, loopHead1, Collections.emptySet(), forbidden, false)) {
			mNested.put(loopHead2, loopHead1);
		}
		forbidden.clear();
		forbidden.add(loopHead2);
		forbidden.add(loopHead1);

		final Deque<IcfgEdge> loopHead2Edges = new ArrayDeque<>(loopHead2.getOutgoingEdges());
		if (mNested.containsKey(loopHead2)) {
			forbidden.add(mNested.get(loopHead2));
		}
		if (!findLoopHeader(loopHead2Edges, loopHead2, loopHead2, Collections.emptySet(), forbidden, false)) {
			mNested.put(loopHead1, loopHead2);
		}
	}

	/**
	 * Find the exittransitions and exitnodes of a loop.
	 *
	 * @param loopHead
	 */
	private void findLoopExits(final IcfgLocation loopHead, final Set<IcfgLocation> forbiddenNodes) {
		for (final IcfgEdge exit : loopHead.getOutgoingEdges()) {
			if (!findLoopHeader(exit, loopHead, loopHead, Collections.emptySet(), forbiddenNodes, false)) {
				mLoopExitNodes.put(loopHead, exit.getTarget());
				mLoopBodies.get(loopHead).setLoopExit(exit.getTarget());
			}
		}
	}

	/**
	 * Get the backbones of a given {@link loop}
	 *
	 * @param loop
	 * @return
	 */
	private Deque<Backbone> getBackbonePath(final Loop loop) {
		final Deque<Backbone> backbones = new ArrayDeque<>();
		final IcfgLocation loopHead = loop.getLoophead();
		final Deque<Backbone> possibleBackbones = new ArrayDeque<>();

		for (final IcfgEdge initialTransition : loopHead.getOutgoingEdges()) {
			final Backbone firstPossibleBackbone = new Backbone(initialTransition);
			possibleBackbones.add(firstPossibleBackbone);
		}

		while (!possibleBackbones.isEmpty()) {
			final Set<IcfgLocation> visited = new HashSet<>();
			final Backbone backbone = possibleBackbones.pop();

			visited.addAll(backbone.getNodes());
			Boolean done = false;

			/**
			 * using a DFS approach. Add a new edge to the backbone if the loopHead can be reached over it.
			 */
			while (!backbone.getPath().getLast().getTarget().equals(loopHead)) {

				final IcfgEdge edge = backbone.getPath().getLast();
				final IcfgLocation target = backbone.getPath().getLast().getTarget();

				/**
				 * if there is an errorlocation in the backbone attach the backbone as errorpath to the loop.
				 */
				if (mErrorLocations.contains(target)) {
					mLogger.debug("FOUND ERROR LOCATIONS");
					final TransFormula errorFormula = calculateFormula(backbone.getPath());
					backbone.setFormula(errorFormula);
					loop.addErrorPath(edge.getTarget(), backbone);
					mLogger.debug("ERROR PATH DONE");
					done = true;
					break;
				}

				if (!findLoopHeader(edge, loopHead, loopHead, Collections.emptySet(), visited, false)
						|| visited.contains(target)) {
					done = true;
					break;
				}

				visited.add(target);

				/**
				 * in case of multiple outgoing edges create more possible backbones.
				 */
				if (!target.getOutgoingEdges().isEmpty()) {
					for (int i = 1; i < target.getOutgoingEdges().size(); i++) {
						final Backbone newPossibleBackbone = new Backbone(backbone);
						newPossibleBackbone.addTransition(target.getOutgoingEdges().get(i));
						possibleBackbones.addLast(newPossibleBackbone);
					}
					backbone.addTransition(target.getOutgoingEdges().get(0));
				}
			}

			if (done) {
				continue;
			}

			final TransFormula tf = calculateFormula(backbone.getPath());
			backbone.setFormula(tf);
			backbones.addLast(backbone);
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
	 * Merge all backbone paths into one and calculate its Transformula.
	 *
	 * @param backbones
	 * @return
	 */
	private Pair<UnmodifiableTransFormula, Set<IcfgEdge>> mergeBackbones(final Deque<Backbone> backbones) {
		final Set<IcfgEdge> path = new HashSet<>();
		UnmodifiableTransFormula loopFormula = (UnmodifiableTransFormula) backbones.getFirst().getFormula();
		for (final Backbone backbone : backbones) {
			path.addAll(backbone.getPath());
			loopFormula = TransFormulaUtils.parallelComposition(mLogger, mServices, 0, mScript, null, false,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, loopFormula,
					(UnmodifiableTransFormula) backbone.getFormula());
		}
		return new Pair<>(loopFormula, path);
	}

	/**
	 * Get Loop bodies of an {@link IIcfg}. As a Queue of loop datastructures
	 */
	public Map<IcfgLocation, Loop> getLoopBodies() {
		return mLoopBodies;
	}
}
