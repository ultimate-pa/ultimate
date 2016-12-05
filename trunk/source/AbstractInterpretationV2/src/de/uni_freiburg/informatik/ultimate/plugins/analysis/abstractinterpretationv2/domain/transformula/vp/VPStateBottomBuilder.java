package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

public class VPStateBottomBuilder extends VPStateBuilder {

	public VPStateBottomBuilder(VPDomain domain) {
		super(domain);
	}

	@Override
	VPState build() {
		return mDomain.getVpStateFactory().getBottomState();
	}
	
}
