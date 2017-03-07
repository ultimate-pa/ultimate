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

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;

public class TermEvaluatorFactory<VALUE extends INonrelationalValue<VALUE>, STATE extends INonrelationalAbstractState<STATE, IProgramVarOrConst>>
		implements ITermEvaluatorFactory<VALUE, STATE, IProgramVarOrConst> {
	
	private final Function<Object, VALUE> mConstantValueExpressionEvaluatorCreator;
	
	public TermEvaluatorFactory(final Function<Object, VALUE> constantValueEvaluatorCreator) {
		mConstantValueExpressionEvaluatorCreator = constantValueEvaluatorCreator;
	}
	
	@Override
	public INaryTermEvaluator<VALUE, STATE, IProgramVarOrConst> createApplicationTerm(final int arity,
			final String operator, final Supplier<STATE> bottomStateSupplier) {
		assert arity >= 0;
		assert operator != null;
		return new ApplicationTermEvaluator<>(arity, operator, bottomStateSupplier);
	}
	
	@Override
	public ITermEvaluator<VALUE, STATE, IProgramVarOrConst> createConstantValueEvaluator(final Object value) {
		assert value != null;
		
		final EvaluatorType evaluatorType;
		if (value instanceof BigInteger) {
			evaluatorType = EvaluatorType.INTEGER;
		} else if (value instanceof BigDecimal) {
			evaluatorType = EvaluatorType.REAL;
		} else if (value instanceof Boolean) {
			evaluatorType = EvaluatorType.BOOL;
		} else {
			throw new IllegalArgumentException("Unknown type: " + value.getClass().getSimpleName());
		}

		return new ConstantTermEvaluator<VALUE, STATE, IProgramVarOrConst>(
				mConstantValueExpressionEvaluatorCreator.apply(value), evaluatorType);
	}
	
	@FunctionalInterface
	public interface Function<NAMETYPE, VALUETYPE> {
		public VALUETYPE apply(final NAMETYPE name);
	}
	
	@Override
	public ITermEvaluator<VALUE, STATE, IProgramVarOrConst> createVariableTermEvaluator(final String variable,
			final Sort sort) {
		return new VariableTermEvaluator<>(variable, sort);
	}
}
