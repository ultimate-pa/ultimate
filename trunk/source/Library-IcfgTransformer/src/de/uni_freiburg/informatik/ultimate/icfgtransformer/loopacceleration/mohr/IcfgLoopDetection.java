package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.mohr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

public class IcfgLoopDetection<INLOC extends IcfgLocation> {

	private final Set<IcfgLoop<INLOC>> mLoops;

	public IcfgLoopDetection(final IIcfg<INLOC> icfg) {
		mLoops = loopExtraction(icfg);
	}

	@SuppressWarnings("unchecked")
	private Set<IcfgLoop<INLOC>> loopExtraction(final IIcfg<INLOC> originalIcfg) {
		final Set<INLOC> init = originalIcfg.getInitialNodes();
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
				dom.put(node, newDom);
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
		for (final IcfgEdge edge : backedges) {
			final INLOC head = (INLOC) edge.getTarget();
			final Set<INLOC> body = new HashSet<>();
			body.add(head);
			final Deque<INLOC> stack = new ArrayDeque<>();
			stack.add((INLOC) edge.getSource());
			while (!stack.isEmpty()) {
				final INLOC node = stack.removeFirst();
				if (!body.contains(node)) {
					body.add(node);
					stack.addAll((Collection<? extends INLOC>) node.getIncomingNodes());
				}
			}
			if (loopbodies.containsKey(head)) {
				loopbodies.get(head).addAll(body);
			} else {
				loopbodies.put(head, new IcfgLoop<>(body, head));
			}
		}

		final ArrayList<INLOC> heads = new ArrayList<>(loopbodies.keySet());
		for (final INLOC nestedhead : heads) {
			for (final INLOC head : heads) {
				if (nestedhead.equals(head) || !loopbodies.containsKey(head)) {
					continue;
				}
				if (loopbodies.get(head).contains(nestedhead)) {
					loopbodies.get(head).addNestedLoop(loopbodies.get(nestedhead));
					loopbodies.remove(nestedhead);
				}
			}
		}
		return new HashSet<>(loopbodies.values());

	}

	public Set<IcfgLoop<INLOC>> getResult() {
		return mLoops;
	}
}
