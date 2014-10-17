package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

import java.util.ArrayList;

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
				ret = bipartiteMatching(nodes);
		}
		return ret;
	}
	private AnnotatedProgramPoint bipartiteMatching(ArrayList<AnnotatedProgramPoint> nodes) {
		return null;
	}
}
