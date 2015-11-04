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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.interval;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.EvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class IntervalLogicalEvaluatorFactory implements
        IEvaluatorFactory<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar> {

	private static final int ARITY_MIN = 1;
	private static final int ARITY_MAX = 2;
	private static final int BUFFER_MAX = 100;

	private final Logger mLogger;
	private final IntervalStateConverter<CodeBlock, IBoogieVar> mStateConverter;

	public IntervalLogicalEvaluatorFactory(Logger logger, IntervalStateConverter<CodeBlock, IBoogieVar> stateConverter) {
		mLogger = logger;
		mStateConverter = stateConverter;
	}

	@Override
	public INAryEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar> createNAryExpressionEvaluator(
	        int arity) {

		assert arity >= ARITY_MIN && arity <= ARITY_MAX;

		switch (arity) {
		case ARITY_MIN:
			return new IntervalLogicalUnaryExpressionEvaluator(mLogger);
		case ARITY_MAX:
			return new IntervalLogicalBinaryExpressionEvaluator(mLogger);
		default:
			final StringBuilder stringBuilder = new StringBuilder(BUFFER_MAX);
			stringBuilder.append("Arity of ").append(arity).append(" is not implemented.");
			throw new UnsupportedOperationException(stringBuilder.toString());
		}
	}

	@Override
	public IEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar> createSingletonValueExpressionEvaluator(
	        String value, Class<?> valueType) {
		assert value != null;

		return new IntervalLogicalSingletonValueExpressionEvaluator(
		        new IntervalDomainValue(new IntervalValue(value), new IntervalValue(value)));
	}

	@Override
	public IEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar> createSingletonVariableExpressionEvaluator(
	        String variableName) {
		assert variableName != null;

		return new IntervalLogicalSingletonVariableExpressionEvaluator(variableName, mStateConverter);
	}

	@Override
	public IEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar> createSingletonLogicalValueExpressionEvaluator(
	        boolean value) {
		return new IntervalLogicalSingletonBooleanExpressionEvaluator(value);
	}

}
