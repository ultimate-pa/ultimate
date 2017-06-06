package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collections;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;

public class EqStateFactory<ACTION extends IIcfgTransition<IcfgLocation>> {

	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;
	private final EqConstraintFactory<ACTION, EqNode, EqFunction> mEqConstraintFactory;
	
	public EqStateFactory(EqNodeAndFunctionFactory eqNodeAndFunctionFactory, 
			EqConstraintFactory<ACTION, EqNode, EqFunction> eqConstraintFactory) {
		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;
		mEqConstraintFactory = eqConstraintFactory;
	}

	public EqState<ACTION> disjoinAll(Set<EqState<ACTION>> statesForCurrentEc) {
		final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> disjunctiveConstraint = 
				mEqConstraintFactory.getDisjunctiveConstraint(
						statesForCurrentEc.stream()
								.map(state -> state.getConstraint())
								.collect(Collectors.toSet()));
		final EqConstraint<ACTION, EqNode, EqFunction> flattenedConstraint = disjunctiveConstraint.flatten();
		return getEqState(flattenedConstraint, flattenedConstraint.getPvocs());
	}

	public EqState<ACTION> getTopState() {
		return getEqState(mEqConstraintFactory.getEmptyConstraint(), Collections.emptySet());
	}

	public EqNodeAndFunctionFactory getEqNodeAndFunctionFactory() {
		return mEqNodeAndFunctionFactory;
	}

//	public EqState<ACTION> getEqState(EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> projectedConstraint,
	public <NODE extends IEqNodeIdentifier<NODE, FUNCTION>, FUNCTION extends IEqFunctionIdentifier<FUNCTION>> 
		EqState<ACTION> getEqState(EqConstraint<ACTION, NODE, FUNCTION> constraint,
			Set<IProgramVarOrConst> newVariables) {
		// TODO something smarter
		return new EqState<>((EqConstraint<ACTION, EqNode, EqFunction>) constraint, mEqNodeAndFunctionFactory, this);
	}

	public EqConstraintFactory<ACTION, EqNode, EqFunction> getEqConstraintFactory() {
		return mEqConstraintFactory;
	}

}
