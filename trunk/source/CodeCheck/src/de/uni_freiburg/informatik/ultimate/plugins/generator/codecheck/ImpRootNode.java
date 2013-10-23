package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.model.structure.BaseLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;

public class ImpRootNode extends AnnotatedProgramPoint {
	
	private static final long serialVersionUID = 1L;

	public ImpRootNode(RootAnnot rootAnnot) {
		super(null,new ProgramPoint("root", "", false, null, null));
		getPayload().getAnnotations().put(Activator.PLUGIN_ID, rootAnnot);
		
	}

	public RootAnnot getRootAnnot() {
		return ((RootAnnot) getPayload().getAnnotations().get(
				Activator.PLUGIN_ID));
	}
	
	@Override
	public String toString() {
		return "root";
	}
}
