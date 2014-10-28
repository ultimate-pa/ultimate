package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.GlobalSettings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.RedirectionStrategy;


public class RedirectionFinder {
	
	private ImpulseChecker codeChecker;
	public RedirectionFinder(ImpulseChecker codeChecker) {
		this.codeChecker = codeChecker;
	}
	
	public AnnotatedProgramPoint getStrongestValidCopy(AppEdge edge) {
		return depthFirstSearch(edge, edge.getTarget());
	}
	private AnnotatedProgramPoint depthFirstSearch(AppEdge edge, AnnotatedProgramPoint clone) {
		ArrayList <AnnotatedProgramPoint> nextNodes = new ArrayList<AnnotatedProgramPoint> ();
		for (AnnotatedProgramPoint nextClone : clone.getNextClones()) {
			if (codeChecker.isValidRedirection(edge, nextClone)) {
				if (GlobalSettings._instance.redirectionStrategy == RedirectionStrategy.FIRST) {
					return depthFirstSearch(edge, nextClone);
				}
				nextNodes.add(depthFirstSearch(edge, nextClone));
			}
		}
		return pickUp(clone, nextNodes);
	}
	private AnnotatedProgramPoint pickUp(AnnotatedProgramPoint def, ArrayList<AnnotatedProgramPoint> nodes) {
		AnnotatedProgramPoint ret = def;
		if (!nodes.isEmpty()) {
			if (GlobalSettings._instance.redirectionStrategy == RedirectionStrategy.RANDOM)
				ret = nodes.get((int) (Math.random() * nodes.size()));
			if (GlobalSettings._instance.redirectionStrategy == RedirectionStrategy.RANDOM_STRONGEST)
				ret = strongRandomPickup(nodes);
		}
		return ret;
	}
	private AnnotatedProgramPoint strongRandomPickup(ArrayList<AnnotatedProgramPoint> nodes) {
		HashSet<AnnotatedProgramPoint> predicates = new HashSet<AnnotatedProgramPoint>();
		for (AnnotatedProgramPoint node : nodes)
			predicates.add(node);
		
		for (AnnotatedProgramPoint node : nodes) {
			if (!predicates.contains(node))
				continue;
			AnnotatedProgramPoint[] comp = predicates.toArray(new AnnotatedProgramPoint[]{});
			for (AnnotatedProgramPoint subNode : comp) {
				if (subNode == node)
					continue;
				if (codeChecker.isStrongerPredicate(node.getPredicate(), subNode.getPredicate()))
					predicates.remove(subNode);
			}
		}
		AnnotatedProgramPoint[] best = predicates.toArray(new AnnotatedProgramPoint[]{});
		return best[(int) (best.length * Math.random())];
	}
}
