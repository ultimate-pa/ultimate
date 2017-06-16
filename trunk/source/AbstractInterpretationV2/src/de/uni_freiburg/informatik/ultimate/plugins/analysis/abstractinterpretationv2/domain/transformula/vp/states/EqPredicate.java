package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IAbstractPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;

public class EqPredicate<ACTION extends IIcfgTransition<IcfgLocation>> implements IAbstractPredicate {

	private final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> mConstraint;
	private final String[] mProcedures;
	private final Set<IProgramVar> mVars;
	
//	public EqPredicate(EqConstraint<ACTION, EqNode, EqFunction> constraint) {
//
//	}

	public EqPredicate(EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> constraint, Set<IProgramVar> vars, 
			String[] procedures) {
		assert vars != null;
		mConstraint = constraint;
		mVars = vars;
		mProcedures = procedures;
	}

	@Override
	public String[] getProcedures() {
		return mProcedures;
	}

	@Override
	public Set<IProgramVar> getVars() {
		return mVars;
	}

	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> getEqConstraint() {
		return mConstraint;
	}

	
	@Override
	public String toString() {
		return mConstraint.toString();
	}
}
