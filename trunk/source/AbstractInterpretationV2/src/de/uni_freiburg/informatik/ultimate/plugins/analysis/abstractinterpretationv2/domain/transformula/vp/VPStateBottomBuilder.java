package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class VPStateBottomBuilder<ACTION extends IIcfgTransition<IcfgLocation>> extends VPStateBuilder<ACTION> {

	boolean mVarsHaveBeenSet = false;

	public VPStateBottomBuilder(final VPDomain<ACTION> domain) {
		super(domain);
	}

	@Override
	public VPStateBuilder<ACTION> setVars(final Set<IProgramVar> vars) {
		mVarsHaveBeenSet = true;
		return super.setVars(vars);
	}

	@Override
	VPStateBottom<ACTION> build() {
		assert mVarsHaveBeenSet;
		final VPStateBottom<ACTION> state = new VPStateBottom<>(mDomain, mVars);
		return state;
	}

}
