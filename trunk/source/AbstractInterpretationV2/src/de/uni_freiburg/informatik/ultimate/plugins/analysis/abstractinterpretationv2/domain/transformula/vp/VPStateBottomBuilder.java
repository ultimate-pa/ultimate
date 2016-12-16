package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class VPStateBottomBuilder extends VPStateBuilder {
	
	boolean mVarsHaveBeenSet = false;

	public VPStateBottomBuilder(VPDomain domain) {
		super(domain);
//		setDisEqualites(Collections.emptySet());
	}
	
//	Set<IProgramVar> mVariables;
	
//	public VPStateBottomBuilder setVariables(Set<IProgramVar> vars) {
////		mVariables = vars;
//		return this;
//	}
	

	@Override
	public VPStateBuilder setVars(Set<IProgramVar> vars) {
		mVarsHaveBeenSet = true;
		return super.setVars(vars);
	}
	
	
	@Override
	VPStateBottom build() {
		assert mVarsHaveBeenSet;
		VPStateBottom state = new VPStateBottom(mDomain, mVars);
		return state;
	}
	
}
