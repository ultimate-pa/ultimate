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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Factory for evaluators of the sign domain.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class SignEvaluatorFactory implements IEvaluatorFactory<SignDomainValue, SignDomainState, CodeBlock> {

	private static final int ARITY_MIN = 1;
	private static final int ARITY_MAX = 2;
	private static final int BUFFER_MAX = 100;
	private final ILogger mLogger;

	public SignEvaluatorFactory(ILogger logger, String evaluatorType, int maxParallelStates) {
		mLogger = logger;
	}

	@Override
	public INAryEvaluator<SignDomainValue, SignDomainState, CodeBlock> createNAryExpressionEvaluator(int arity,
			EvaluatorType type) {

		assert arity >= ARITY_MIN && arity <= ARITY_MAX;

		switch (arity) {
		case ARITY_MIN:
			return new SignUnaryExpressionEvaluator();
		case ARITY_MAX:
			return new SignBinaryExpressionEvaluator(mLogger, type);
		default:
			final StringBuilder stringBuilder = new StringBuilder(BUFFER_MAX);
			stringBuilder.append("Arity of ").append(arity).append(" is not implemented.");
			throw new UnsupportedOperationException(stringBuilder.toString());
		}
	}

	@Override
	public IEvaluator<SignDomainValue, SignDomainState, CodeBlock> createSingletonValueExpressionEvaluator(String value,
			Class<?> valueType) {

		if (valueType.equals(BigInteger.class)) {
			return new SignSingletonIntegerExpressionEvaluator(value);
		}

		if (valueType.equals(BigDecimal.class)) {
			return new SignSingletonDecimalExpressionEvaluator(value);
		}

		throw new UnsupportedOperationException("The type " + valueType.toString() + " is not supported.");
	}

	@Override
	public IEvaluator<SignDomainValue, SignDomainState, CodeBlock>
			createSingletonVariableExpressionEvaluator(IBoogieVar variableName) {
		return new SignSingletonVariableExpressionEvaluator(variableName);
	}

	@Override
	public IEvaluator<SignDomainValue, SignDomainState, CodeBlock>
			createSingletonLogicalValueExpressionEvaluator(BooleanValue value) {
		throw new UnsupportedOperationException("not implemented");
	}

	@Override
	public IEvaluator<SignDomainValue, SignDomainState, CodeBlock> createFunctionEvaluator(String functionName,
			int inputParamCount) {
		throw new UnsupportedOperationException("not implemented");
	}

	@Override
	public IEvaluator<SignDomainValue, SignDomainState, CodeBlock> createConditionalEvaluator() {
		throw new UnsupportedOperationException("not implemented");
	}

	@Override
	public IEvaluator<SignDomainValue, SignDomainState, CodeBlock> createSingletonValueTopEvaluator() {
		throw new UnsupportedOperationException("not implemented");
	}
}
