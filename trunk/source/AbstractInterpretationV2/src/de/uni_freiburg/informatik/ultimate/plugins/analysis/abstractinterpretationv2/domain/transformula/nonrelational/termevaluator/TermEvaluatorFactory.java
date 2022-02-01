/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.termevaluator;

import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorLogger;

public class TermEvaluatorFactory<VALUE extends INonrelationalValue<VALUE>, STATE extends NonrelationalState<STATE, VALUE>>
		implements ITermEvaluatorFactory<VALUE, STATE> {

	private final Function<Object, VALUE> mConstantValueExpressionEvaluatorCreator;
	private final int mMaxParallelStates;
	private final INonrelationalValueFactory<VALUE> mNonrelationalValueFactory;
	private final EvaluatorLogger mEvaluatorLogger;

	public TermEvaluatorFactory(final ILogger logger, final int maxParallelStates,
			final Function<Object, VALUE> constantValueEvaluatorCreator,
			final INonrelationalValueFactory<VALUE> nonrelationalValueFactory) {
		mMaxParallelStates = maxParallelStates;
		mConstantValueExpressionEvaluatorCreator = constantValueEvaluatorCreator;
		mNonrelationalValueFactory = nonrelationalValueFactory;
		mEvaluatorLogger = new EvaluatorLogger(logger);
	}

	@Override
	public INaryTermEvaluator<VALUE, STATE> createApplicationTerm(final int arity, final String operator,
			final INonrelationalValueFactory<VALUE> nonrelationalValueFactory,
			final Supplier<STATE> bottomStateSupplier) {
		assert arity >= 0;
		assert operator != null;
		return new ApplicationTermEvaluator<>(mEvaluatorLogger, arity, operator, mMaxParallelStates,
				nonrelationalValueFactory, bottomStateSupplier);
	}

	@Override
	public ITermEvaluator<VALUE, STATE> createConstantValueEvaluator(final Object value) {
		assert value != null;
		return new ConstantTermEvaluator<>(mConstantValueExpressionEvaluatorCreator.apply(value));
	}

	@FunctionalInterface
	public interface Function<NAMETYPE, VALUETYPE> {
		public VALUETYPE apply(final NAMETYPE name);
	}

	@Override
	public ITermEvaluator<VALUE, STATE> createVariableTermEvaluator(final String variable, final Sort sort) {
		return new VariableTermEvaluator<>(variable, sort, mNonrelationalValueFactory);
	}
}
