package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNodeAndFunctionFactory;

public class EqStateFactory<ACTION extends IIcfgTransition<IcfgLocation>> {

	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;
	private final EqConstraintFactory<ACTION, EqNode, EqFunction> mEqConstraintFactory;
	
	public EqStateFactory(EqNodeAndFunctionFactory eqNodeAndFunctionFactory, 
			EqConstraintFactory<ACTION, EqNode, EqFunction> eqConstraintFactory) {
		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;
		mEqConstraintFactory = eqConstraintFactory;
	}

	public EqState<ACTION> disjoinAll(Set<EqState<ACTION>> statesForCurrentEc) {
		// TODO Auto-generated method stub
		return null;
	}

	public EqState<ACTION> getTopState(Set<Object> emptySet) {
		// TODO Auto-generated method stub
		return null;
	}

	public EqNodeAndFunctionFactory getEqNodeAndFunctionFactory() {
		return mEqNodeAndFunctionFactory;
	}

//	public EqState<ACTION> getEqState(EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> projectedConstraint,
	public EqState<ACTION> getEqState(EqConstraint<ACTION, EqNode, EqFunction> projectedConstraint,
			Set<IProgramVarOrConst> newVariables) {
		// TODO Auto-generated method stub
		return null;
	}

	public EqConstraintFactory<ACTION, EqNode, EqFunction> getEqConstraintFactory() {
		return mEqConstraintFactory;
	}

}
