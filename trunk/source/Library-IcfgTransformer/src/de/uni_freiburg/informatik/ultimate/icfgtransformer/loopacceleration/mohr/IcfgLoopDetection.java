/*
 * Copyright (C) 2017 Moritz Mohr (mohrm@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.mohr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermClassifier;

public class IcfgLoopDetection<INLOC extends IcfgLocation> {

	private final Set<IcfgLoop<INLOC>> mLoops;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	public IcfgLoopDetection(final ILogger logger, final IUltimateServiceProvider services, final IIcfg<INLOC> icfg) {
		mLogger = logger;
		mServices = services;
		mLoops = loopExtraction(icfg);
	}

	@SuppressWarnings("unchecked")
	private Set<IcfgLoop<INLOC>> loopExtraction(final IIcfg<INLOC> originalIcfg) {
		final Set<INLOC> init = originalIcfg.getInitialNodes();

		if (init.size() > 1) {
			mLogger.info("Unable to accelerate with more than one entries");
			return new HashSet<IcfgLoop<INLOC>>();
		}

		final Deque<INLOC> open = new ArrayDeque<>();
		final Map<INLOC, Set<INLOC>> dom = new HashMap<>();

		// Determine dominating nodes
		for (final INLOC entry : init) {
			final Set<INLOC> newDom = new HashSet<>();
			newDom.add(entry);
			dom.put(entry, newDom);
			for (final IcfgLocation successor : entry.getOutgoingNodes()) {
				if (!open.contains(successor)) {
					open.add((INLOC) successor);
				}
			}
		}

		while (!open.isEmpty()) {
			final INLOC node = open.removeFirst();
			final Set<INLOC> newDom = new HashSet<>();
			for (final IcfgLocation predecessor : node.getIncomingNodes()) {
				if (dom.containsKey(predecessor)) {
					if (newDom.isEmpty()) {
						newDom.addAll(dom.get(predecessor));
					} else {
						newDom.retainAll(dom.get(predecessor));
					}
				}
			}
			if (!newDom.isEmpty()) {
				newDom.add(node);
			}
			if (!newDom.equals(dom.get(node))) {
				for (final IcfgLocation successor : node.getOutgoingNodes()) {
					if (!open.contains(successor)) {
						open.add((INLOC) successor);
					}
				}
				if (dom.containsKey(node)) {
					dom.get(node).addAll(newDom);
				} else {
					dom.put(node, newDom);
				}
			}

		}
		// Find loopbodies
		final Set<IcfgEdge> backedges = new HashSet<>();
		final Set<INLOC> visited = new HashSet<>();
		open.addAll(originalIcfg.getInitialNodes());
		// Find backedges
		while (!open.isEmpty()) {
			final INLOC node = open.removeFirst();
			visited.add(node);
			for (final IcfgEdge edge : node.getOutgoingEdges()) {
				if (dom.get(node).contains(edge.getTarget())) {
					backedges.add(edge);
				}
				if (!visited.contains(edge.getTarget())) {
					open.add((INLOC) edge.getTarget());
				}
			}
		}
		// Find loopbody
		final Map<INLOC, IcfgLoop<INLOC>> loopbodies = new HashMap<>();
		final Set<INLOC> badLoops = new HashSet<>();
		for (final IcfgEdge edge : backedges) {
			final TermClassifier tc = new TermClassifier();
			final INLOC head = (INLOC) edge.getTarget();
			final Set<INLOC> body = new HashSet<>();
			body.add(head);
			final Deque<INLOC> queue = new ArrayDeque<>();
			queue.add((INLOC) edge.getSource());
			tc.checkTerm(edge.getTransformula().getFormula());
			while (!queue.isEmpty()) {
				final INLOC node = queue.removeFirst();
				if (!body.contains(node)) {
					body.add(node);
					queue.addAll((Collection<? extends INLOC>) node.getIncomingNodes());
					node.getIncomingEdges().forEach(e -> tc.checkTerm(e.getTransformula().getFormula()));
				}
			}
			if (tc.hasArrays()) {
				badLoops.add(head);
				mLogger.info("Unable to accelerate loop at node " + head + " since it contains array access.");
			} else if (loopbodies.containsKey(head)) {
				loopbodies.get(head).addAll(body);
			} else {
				loopbodies.put(head, new IcfgLoop<>(mServices, body, head));
			}
		}

		badLoops.forEach(loopbodies::remove);

		final ArrayList<INLOC> heads = new ArrayList<>(loopbodies.keySet());
		for (final INLOC nestedhead : heads) {
			for (final INLOC head : heads) {
				if (nestedhead.equals(head) || !loopbodies.containsKey(nestedhead) || !loopbodies.containsKey(head)) {
					continue;
				}
				if (loopbodies.get(head).contains(nestedhead)) {
					loopbodies.get(head).addNestedLoop(loopbodies.get(nestedhead));
					loopbodies.remove(nestedhead);
					mLogger.info("Unable to accelerate, since loop contains nested loops");
					return new HashSet<IcfgLoop<INLOC>>();
				}
			}
		}

		if (loopbodies.isEmpty() && badLoops.isEmpty()) {
			return altLoopExtraction(originalIcfg);
		}

		return new HashSet<>(loopbodies.values());

	}

	@SuppressWarnings("unchecked")
	private Set<IcfgLoop<INLOC>> altLoopExtraction(final IIcfg<INLOC> originalIcfg) {
		final Set<IcfgLoop<INLOC>> result = new HashSet<>();
		final Set<INLOC> loopHeaders = originalIcfg.getLoopLocations();
		for (final INLOC head : loopHeaders) {
			final Set<INLOC> loopBody = new HashSet<>();
			final Deque<List<IcfgEdge>> paths = new ArrayDeque<>();
			for (final IcfgEdge e : head.getOutgoingEdges()) {
				paths.addLast(new ArrayList<>(Arrays.asList(e)));
			}
			while (!paths.isEmpty()) {
				final List<IcfgEdge> path = paths.pop();
				if (path.get(path.size() - 1).getTarget().equals(head)) {
					path.forEach(edge -> loopBody.add((INLOC) edge.getSource()));
					continue;
				}
				for (final IcfgEdge e : path.get(path.size() - 1).getTarget().getOutgoingEdges()) {
					final List<IcfgEdge> newPath = new ArrayList<>(path);
					newPath.add(e);
					paths.addLast(newPath);
				}
			}
			result.add(new IcfgLoop<INLOC>(mServices, loopBody, head));
		}
		return result;
	}

	public Set<IcfgLoop<INLOC>> getResult() {
		mLoops.forEach(l -> mLogger.info("Loop @"+l.getHead()+": "+l.getLoopbody()+"; nested @"+l.getNestedLoopHeads()));
		return mLoops;
	}
}
