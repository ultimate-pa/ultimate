package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class EqFunction implements IEqFunctionIdentifier<EqFunction> {

	public boolean isGlobal() {
		// TODO Auto-generated method stub
		return false;
	}

	public String getProcedure() {
		// TODO Auto-generated method stub
		return null;
	}

	public Term getTerm() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public EqFunction renameVariables(Map<Term, Term> substitutionMapping) {
		// TODO Auto-generated method stub
		return null;
	}

	public IProgramVarOrConst getPvoc() {
		// TODO Auto-generated method stub
		return null;
	}

	public static String getFunctionName() {
		// TODO Auto-generated method stub
		return null;
	}

}
