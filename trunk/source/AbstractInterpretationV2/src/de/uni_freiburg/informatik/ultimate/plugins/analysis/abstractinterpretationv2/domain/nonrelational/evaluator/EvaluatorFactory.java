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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

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
		implements IEvaluatorFactory<VALUE, STATE, CodeBlock> {

	private static final int ARITY_MIN = 1;
	private static final int ARITY_MAX = 2;
	private static final int BUFFER_MAX = 100;

	private final int mMaxParallelStates;
	private final EvaluatorLogger mEvalLogger;

	private final INonrelationalValueFactory<VALUE> mNonrelationalValueFactory;
	private final Function<String, VALUE> mSingletonValueExpressionEvaluatorCreator;

	public EvaluatorFactory(final ILogger logger, final int maxParallelStates,
			final INonrelationalValueFactory<VALUE> nonrelationalValueFactory,
			final Function<String, VALUE> singletonValueEvaluatorCreator) {
		mMaxParallelStates = maxParallelStates;
		mNonrelationalValueFactory = nonrelationalValueFactory;
		mSingletonValueExpressionEvaluatorCreator = singletonValueEvaluatorCreator;
		mEvalLogger = new EvaluatorLogger(logger);
	}

	@Override
	public INAryEvaluator<VALUE, STATE, CodeBlock> createNAryExpressionEvaluator(final int arity,
			final EvaluatorType type) {
		assert arity >= ARITY_MIN && arity <= ARITY_MAX;

		switch (arity) {
		case ARITY_MIN:
			return new UnaryExpressionEvaluator<>(mEvalLogger, mNonrelationalValueFactory);
		case ARITY_MAX:
			return new BinaryExpressionEvaluator<>(mEvalLogger, type, mMaxParallelStates, mNonrelationalValueFactory);
		default:
			throw new UnsupportedOperationException(new StringBuilder(BUFFER_MAX).append("Arity of ").append(arity)
					.append(" is not implemented.").toString());
		}
	}

	@Override
	public IEvaluator<VALUE, STATE, CodeBlock> createFunctionEvaluator(final String functionName,
			final int inputParamCount) {
		return new FunctionEvaluator<>(functionName, inputParamCount, mNonrelationalValueFactory);
	}

	@Override
	public IEvaluator<VALUE, STATE, CodeBlock> createConditionalEvaluator() {
		return new ConditionalEvaluator<>(mNonrelationalValueFactory);
	}

	@Override
	public IEvaluator<VALUE, STATE, CodeBlock> createSingletonValueTopEvaluator() {
		return new SingletonValueExpressionEvaluator<>(mNonrelationalValueFactory.createTopValue());
	}

	@Override
	public IEvaluator<VALUE, STATE, CodeBlock> createSingletonValueExpressionEvaluator(final String value,
			final Class<?> valueType) {
		assert value != null;
		return new SingletonValueExpressionEvaluator<>(
				mSingletonValueExpressionEvaluatorCreator.apply(value, valueType));
	}

	@Override
	public IEvaluator<VALUE, STATE, CodeBlock>
			createSingletonVariableExpressionEvaluator(final IBoogieVar variableName) {
		assert variableName != null;
		return new SingletonVariableExpressionEvaluator<>(variableName, mNonrelationalValueFactory);
	}

	@Override
	public IEvaluator<VALUE, STATE, CodeBlock>
			createSingletonLogicalValueExpressionEvaluator(final BooleanValue value) {
		return new SingletonBooleanExpressionEvaluator<>(value, mNonrelationalValueFactory);
	}

	@FunctionalInterface
	public interface Function<NAMETYPE, VALUETYPE> {
		public VALUETYPE apply(final NAMETYPE name, final Class<?> type);
	}
}
