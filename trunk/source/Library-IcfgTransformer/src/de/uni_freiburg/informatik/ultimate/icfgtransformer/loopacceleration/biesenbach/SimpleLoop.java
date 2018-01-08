package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

public class SimpleLoop {

	final public UnmodifiableTransFormula mLoopTransFormula;
	final public IcfgLocation mHeadNode;
	final public List<Entry<UnmodifiableTransFormula, IcfgLocation>> mExitEdges;
	
	public SimpleLoop(UnmodifiableTransFormula loopTransFormula, IcfgLocation headNode
			, List<Entry<UnmodifiableTransFormula, IcfgLocation>> exitEdges){
		mLoopTransFormula = loopTransFormula;
		mHeadNode = headNode;
		mExitEdges = exitEdges;
	}
}
