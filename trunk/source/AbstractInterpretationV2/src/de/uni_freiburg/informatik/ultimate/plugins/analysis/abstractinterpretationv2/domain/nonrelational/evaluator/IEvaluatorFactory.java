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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;

/**
 * Interface to create {@link IEvaluator}s for different abstract domains.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <VALUE>
 *            The type of the domain's values.
 * @param <STATE>
 *            The type of the abstract state to be used for the evaluators.
 * @param <VARDECL>
 *            Any declaration type.
 */
public interface IEvaluatorFactory<VALUE extends INonrelationalValue<VALUE>, STATE extends IAbstractState<STATE>> {

	/**
	 * Creates an n-ary evaluator for n-ary expressions.
	 *
	 * @param arity
	 *            The arity of the evaluator.
	 * @param type
	 *            The type of the evaluator.
	 * @return A new {@link NAryEvaluator}.
	 */
	NAryEvaluator<VALUE, STATE> createNAryExpressionEvaluator(final int arity, final EvaluatorType type);

	/**
	 * Creates a function evaluator for expressions that contain functions.
	 *
	 * @param functionName
	 *            The name of the function.
	 * @param inputParamCount
	 *            The number of input parameters of the function.
	 * @return A new {@link Evaluator}.
	 */
	Evaluator<VALUE, STATE> createFunctionEvaluator(final String functionName, final int inputParamCount,
			EvaluatorType type);

	/**
	 * @return A new conditional evaluator.
	 */
	Evaluator<VALUE, STATE> createConditionalEvaluator();

	/**
	 * Creates an evaluator that represents the top value.
	 *
	 * @return A new {@link Evaluator}.
	 */
	Evaluator<VALUE, STATE> createSingletonValueTopEvaluator(final EvaluatorType type);

	/**
	 * Creates an evaluator for single values that are occurring in expressions.
	 *
	 * @param value
	 *            The value.
	 * @param valueType
	 *            The type of the value.
	 * @return A new {@link Evaluator}.
	 */
	Evaluator<VALUE, STATE> createSingletonValueExpressionEvaluator(final String value, final Class<?> valueType);

	/**
	 * Creates an evaluator for single variables that are occurring in expressions.
	 *
	 * @param variableName
	 *            The name of the variable.
	 * @return A new {@link Evaluator}.
	 */
	Evaluator<VALUE, STATE> createSingletonVariableExpressionEvaluator(final IProgramVarOrConst variableName);

	/**
	 * Creates an evaluator for single boolean values that are occurring in expressions.
	 *
	 * @param value
	 *            The boolean value.
	 * @return A new {@link Evaluator}.
	 */
	Evaluator<VALUE, STATE> createSingletonLogicalValueExpressionEvaluator(final BooleanValue value);
}
