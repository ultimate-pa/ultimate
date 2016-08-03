package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.paralleldfg;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefGraphAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class ParallelDfgGeneratorObserver extends BaseObserver {

	@Override
	public boolean process(IElement root) throws Throwable {
		
		// rootNode is the dummy note with edges leading to every procedure entry point
		RootNode r = (RootNode) root;
		RCFGEdge out1 = r.getOutgoingEdges().get(0);
		RCFGNode node = out1.getTarget();
		RCFGEdge edge = node.getOutgoingEdges().get(0);
		
		// typically our nodes are also ProgramPoints (roughly: locations)
		ProgramPoint pp = (ProgramPoint) node;

		// typically our nodes are also CodeBlocks (roughly: statements)
		CodeBlock cb = (CodeBlock) edge;
		
		
		// get an annotation through edge->payload->annotations[keyword]
		IAnnotations annot = edge.getPayload().getAnnotations().get("ReachingDefinition Default");
//		IAnnotations annot = edge.getPayload().getAnnotations().get(ReachDefGraphAnnotationProvider.sAnnotationName);
		return false;
	}

}
