package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqTransitionRelation;

public class TransFormulaConverter<ACTION extends IIcfgTransition<IcfgLocation>> {

	private EqConstraintFactory<ACTION, EqNode, EqFunction> eqConstraintFactory;
	private EqNodeAndFunctionFactory eqNodeAndFunctionFactory;

	public EqTransitionRelation<ACTION> getEqTransitionRelationFromTransformula(TransFormula tf) {
		return new ConvertTransformulaToEqTransitionRelation<ACTION>(tf, 
				eqConstraintFactory, eqNodeAndFunctionFactory)
				.getResult();
	}
}
