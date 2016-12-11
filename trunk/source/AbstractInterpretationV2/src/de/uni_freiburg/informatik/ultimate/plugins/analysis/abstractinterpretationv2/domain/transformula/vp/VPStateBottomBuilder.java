package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class VPStateBottomBuilder extends VPStateBuilder {

	public VPStateBottomBuilder(VPDomain domain) {
		super(domain);
		setDisEqualites(Collections.emptySet());
	}
	
	Set<IProgramVar> mVariables;
	
	public VPStateBottomBuilder setVariables(Set<IProgramVar> vars) {
		mVariables = vars;
		return this;
	}
	

	@Override
	VPStateBottom build() {
		assert mVariables != null;
		VPStateBottom state = new VPStateBottom(mDomain);
		state.addVariables(mVariables);
		return state;
	}
	
}
