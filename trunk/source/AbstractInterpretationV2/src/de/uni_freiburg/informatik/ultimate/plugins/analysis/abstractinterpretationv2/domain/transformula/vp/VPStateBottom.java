package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

/**
*
* @author Yu-Wen Chen (yuwenchen1105@gmail.com)
*
*/
public class VPStateBottom extends VPState {
	
	VPStateBottom(VPDomain domain) {
		super(domain);
	}
	
	@Override
	public boolean isBottom() {
		return true;
	}

	@Override
	public String toLogString() {
		return "Bottom reached.";
	}
}
