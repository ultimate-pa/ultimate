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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;

/**
 * Factory for evaluators in the nonrelational abstract domain.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <VALUE>
 *            The type of values of the abstract domain.
 * @param <STATE>
 *            The type of states of the abstract domain.
 */
public class EvaluatorFactory<VALUE extends INonrelationalValue<VALUE>, STATE extends NonrelationalState<STATE, VALUE>>
		implements IEvaluatorFactory<VALUE, STATE> {

	private static final int ARITY_MIN = 1;
	private static final int ARITY_MAX = 2;
	private static final int BUFFER_MAX = 100;

	private final int mMaxParallelStates;
	private final int mMaxRecursionDepth;
	private final EvaluatorLogger mEvalLogger;

	private final INonrelationalValueFactory<VALUE> mNonrelationalValueFactory;
	private final Function<String, VALUE> mSingletonValueExpressionEvaluatorCreator;

	public EvaluatorFactory(final ILogger logger, final int maxParallelStates, final int maxRecursionDepth,
			final INonrelationalValueFactory<VALUE> nonrelationalValueFactory,
			final Function<String, VALUE> singletonValueEvaluatorCreator) {
		mMaxParallelStates = maxParallelStates;
		mMaxRecursionDepth = maxRecursionDepth;
		mNonrelationalValueFactory = nonrelationalValueFactory;
		mSingletonValueExpressionEvaluatorCreator = singletonValueEvaluatorCreator;
		mEvalLogger = new EvaluatorLogger(logger);
	}

	@Override
	public NAryEvaluator<VALUE, STATE> createNAryExpressionEvaluator(final int arity, final EvaluatorType type) {
		assert arity >= ARITY_MIN && arity <= ARITY_MAX;

		switch (arity) {
		case ARITY_MIN:
			return new UnaryExpressionEvaluator<>(mEvalLogger, mMaxRecursionDepth, mNonrelationalValueFactory);
		case ARITY_MAX:
			return new BinaryExpressionEvaluator<>(mEvalLogger, type, mMaxParallelStates, mMaxRecursionDepth,
					mNonrelationalValueFactory);
		default:
			throw new UnsupportedOperationException(new StringBuilder(BUFFER_MAX).append("Arity of ").append(arity)
					.append(" is not implemented.").toString());
		}
	}

	@Override
	public Evaluator<VALUE, STATE> createFunctionEvaluator(final String functionName, final int inputParamCount,
			final EvaluatorType type) {
		return new FunctionEvaluator<>(functionName, inputParamCount, mMaxRecursionDepth, mNonrelationalValueFactory,
				type, mEvalLogger);
	}

	@Override
	public Evaluator<VALUE, STATE> createConditionalEvaluator() {
		return new ConditionalEvaluator<>(mMaxRecursionDepth, mNonrelationalValueFactory, mEvalLogger);
	}

	@Override
	public Evaluator<VALUE, STATE> createSingletonValueTopEvaluator(final EvaluatorType type) {
		return new SingletonValueExpressionEvaluator<>(mNonrelationalValueFactory.createTopValue(), type,
				mMaxParallelStates, mNonrelationalValueFactory, mEvalLogger);
	}

	@Override
	public Evaluator<VALUE, STATE> createSingletonValueExpressionEvaluator(final String value,
			final Class<?> valueType) {
		assert value != null;
		final EvaluatorType evaluatorType;
		if (valueType == BigInteger.class) {
			evaluatorType = EvaluatorType.INTEGER;
		} else if (valueType == BigDecimal.class) {
			evaluatorType = EvaluatorType.REAL;
		} else if (valueType == Boolean.class) {
			evaluatorType = EvaluatorType.BOOL;
		} else {
			throw new IllegalArgumentException("Unknown type " + valueType);
		}
		return new SingletonValueExpressionEvaluator<>(
				mSingletonValueExpressionEvaluatorCreator.apply(value, valueType), evaluatorType, mMaxRecursionDepth,
				mNonrelationalValueFactory, mEvalLogger);
	}

	@Override
	public Evaluator<VALUE, STATE> createSingletonVariableExpressionEvaluator(final IProgramVarOrConst variableName) {
		assert variableName != null;
		return new SingletonVariableExpressionEvaluator<>(variableName, mMaxRecursionDepth, mNonrelationalValueFactory,
				mEvalLogger);
	}

	@Override
	public Evaluator<VALUE, STATE> createSingletonLogicalValueExpressionEvaluator(final BooleanValue value) {
		return new SingletonBooleanExpressionEvaluator<>(value, mMaxRecursionDepth, mNonrelationalValueFactory,
				mEvalLogger);
	}

	@FunctionalInterface
	public interface Function<NAMETYPE, VALUETYPE> {
		public VALUETYPE apply(final NAMETYPE name, final Class<?> type);
	}
}
