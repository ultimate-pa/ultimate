package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Collections;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class VPTfExtraArrayIdentifier extends VPTfArrayIdentifier {

	public VPTfExtraArrayIdentifier(IProgramVarOrConst pvoc, ArrayInOutStatus inOutStatus) {
		super(pvoc, inOutStatus);
	}

	@Override
	public Map<IProgramVar, TermVariable> getInVars() {
		if (getProgramVarOrConst() instanceof IProgramVar 
				&& isInOrThrough()) {
			return Collections.singletonMap((IProgramVar) getProgramVarOrConst(), null);
		} else {
			return Collections.emptyMap();
		}
	}

	@Override
	public Map<IProgramVar, TermVariable> getOutVars() {
		if (getProgramVarOrConst() instanceof IProgramVar 
				&& isInOrThrough()) {
			return Collections.singletonMap((IProgramVar) getProgramVarOrConst(), null);
		} else {
			return Collections.emptyMap();
		}
	}

	
}
