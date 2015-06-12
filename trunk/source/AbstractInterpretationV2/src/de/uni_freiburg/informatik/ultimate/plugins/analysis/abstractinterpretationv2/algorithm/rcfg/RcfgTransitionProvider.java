package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;

public class RcfgTransitionProvider implements ITransitionProvider<RCFGEdge>{
	
	@Override
	public Collection<RCFGEdge> getSuccessors(RCFGEdge elem) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isPostErrorLocation(RCFGEdge elem) {
		// TODO Auto-generated method stub
		return false;
	}

}
