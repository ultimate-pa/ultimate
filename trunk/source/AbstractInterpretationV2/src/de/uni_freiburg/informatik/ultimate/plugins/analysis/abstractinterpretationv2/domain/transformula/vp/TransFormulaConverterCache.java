/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
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

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 */
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
