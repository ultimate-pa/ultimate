package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;


enum Strategy {
	FIRST, RANDOM, RANDOM_STRONGEST;
}

public class RedirectionFinder {
	
	private ImpulseChecker codeChecker;
	private final Strategy strategy;
	public RedirectionFinder(ImpulseChecker codeChecker) {
		this.codeChecker = codeChecker;
		strategy = Strategy.RANDOM;
	}
	
	public AnnotatedProgramPoint getStrongestValidCopy(AppEdge edge) {
		return depthFirstSearch(edge, edge.getTarget());
	}
	private AnnotatedProgramPoint depthFirstSearch(AppEdge edge, AnnotatedProgramPoint clone) {
		ArrayList <AnnotatedProgramPoint> nextNodes = new ArrayList<AnnotatedProgramPoint> ();
		for (AnnotatedProgramPoint nextClone : clone.getNextClones()) {
			if (codeChecker.isValidRedirection(edge, nextClone)) {
				if (strategy == Strategy.FIRST) {
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
			if (strategy == Strategy.RANDOM)
				ret = nodes.get((int) (Math.random() * nodes.size()));
			if (strategy == Strategy.RANDOM_STRONGEST)
				ret = bipartiteMatching(nodes);
		}
		return ret;
	}
	private AnnotatedProgramPoint bipartiteMatching(ArrayList<AnnotatedProgramPoint> nodes) {
		return null;
	}
}
