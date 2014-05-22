package de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

public class AppHyperEdge extends AppEdge {
	
	private static final long serialVersionUID = 1L;
	
	AnnotatedProgramPoint hier;
	Return returnStm;

	public AppHyperEdge(AnnotatedProgramPoint source, AnnotatedProgramPoint hier, Return returnStm,
			AnnotatedProgramPoint target) {
		super(source, returnStm, target);
		this.hier = hier;
		this.returnStm = returnStm;
	}
	
	public AnnotatedProgramPoint getHier() {
		return hier;
	}

	@Override
	public void disconnect() {
		this.hier.getOutgoingHyperEdges().remove(this);
		this.hier = null;
		super.disconnect();
	}
}
