package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

public class SimpleLoop {

	final public UnmodifiableTransFormula mLoopTransFormula;
	final public IcfgLocation mHeadNode;
	final public List<IcfgEdge> mExitEdges;
	
	public SimpleLoop(UnmodifiableTransFormula loopTransFormula, IcfgLocation headNode, List<IcfgEdge> exitEdges){
		mLoopTransFormula = loopTransFormula;
		mHeadNode = headNode;
		mExitEdges = exitEdges;
	}
}
