package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqTransitionRelation;

public class TransFormulaConverterCache<ACTION extends IIcfgTransition<IcfgLocation>> {

	private EqConstraintFactory<ACTION, EqNode, EqFunction> mEqConstraintFactory;
	private EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;
	
	private final Map<TransFormula, EqTransitionRelation<ACTION>> mTransformulaToEqTransitionRelationCache =
			new HashMap<>();
	private final VPDomainPreanalysis mPreAnalysis;
	
	public TransFormulaConverterCache(EqNodeAndFunctionFactory eqNodeAndFunctionFactory, 
			EqConstraintFactory<ACTION, EqNode, EqFunction> eqConstraintFactory, VPDomainPreanalysis preAnalysis) {
		
		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;
		mEqConstraintFactory = eqConstraintFactory;
		mPreAnalysis = preAnalysis;
	}

	public EqTransitionRelation<ACTION> getEqTransitionRelationFromTransformula(TransFormula tf) {
		EqTransitionRelation<ACTION> result = mTransformulaToEqTransitionRelationCache.get(tf);
		if (result == null) {
			result = new ConvertTransformulaToEqTransitionRelation<ACTION>(tf, 
					mEqConstraintFactory, mEqNodeAndFunctionFactory, mPreAnalysis)
				.getResult();
			mTransformulaToEqTransitionRelationCache.put(tf, result);
		}
		return result;
	}
}
