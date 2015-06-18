package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.RCFGLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

public class RcfgLoopDetector implements ILoopDetector<CodeBlock> {

	private HashMap<ProgramPoint, HashMap<RCFGEdge, RCFGEdge>> mLoops;

	public RcfgLoopDetector(RCFGLoopDetector loopDetector) {
		mLoops = loopDetector.getResult();
	}

	@Override
	public CodeBlock getLoopExit(CodeBlock transition) {
		assert transition != null;
		final RCFGNode source = transition.getSource();
		final HashMap<RCFGEdge, RCFGEdge> loops = mLoops.get(source);
		if (loops == null) {
			return null;
		}
		final RCFGEdge exit = loops.get(transition);
		if (exit instanceof CodeBlock) {
			return (CodeBlock) exit;
		}
		assert exit == null;
		return null;
	}

}
