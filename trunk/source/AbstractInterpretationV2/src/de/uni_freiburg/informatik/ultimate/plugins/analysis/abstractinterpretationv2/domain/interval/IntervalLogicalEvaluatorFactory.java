/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Evaluator factory for logical evaluators in the {@link IntervalDomain}.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalLogicalEvaluatorFactory implements IEvaluatorFactory<IntervalDomainValue, CodeBlock, BoogieVar> {
	
	private final IntervalStateConverter<CodeBlock, BoogieVar> mStateConverter;
	
	public IntervalLogicalEvaluatorFactory(IntervalStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mStateConverter = stateConverter;
	}
	
	@Override
	public INAryEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> createNAryExpressionEvaluator(int arity) {

		assert arity >= 1 && arity <= 2;

		switch (arity) {
		case 1:
			return new IntervalLogicalUnaryExpressionEvaluator();
		case 2:
			return new IntervalLogicalBinaryExpressionEvaluator();
		default:
			throw new UnsupportedOperationException(
			        "The arity " + arity + " is not implemented for logical evaluators.");
		}
	}

	@Override
	public IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> createSingletonValueExpressionEvaluator(String value,
	        Class<?> valueType) {
		assert value != null;
		
		return new IntervalLogicalSingletonValueExpressionEvaluator(
		        new IntervalDomainValue(new IntervalValue(value), new IntervalValue(value)));
	}

	@Override
	public IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> createSingletonVariableExpressionEvaluator(
	        String variableName) {
		assert variableName != null;

		return new IntervalLogicalSingletonVariableExpressionEvaluator(variableName, mStateConverter);
	}

}