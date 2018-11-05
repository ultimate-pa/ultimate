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

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;

/**
 * Default interface for an expression evaluator. Each Evaluator should implement this interface in order to allow for
 * expressions to be evaluated.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <VALUE>
 *            The value type of the abstract domain.
 * @param <ACTION>
 *            Any action type.
 * @param <VARDECL>
 *            Any variable declaration type.
 */
public interface IEvaluator<VALUE, STATE extends IAbstractState<STATE>> {

	/**
	 * Evaluates the evaluator with all its sub-evaluators according to the given state.
	 *
	 * @param currentState
	 *            The originating state to evaluate from.
	 * @param currentRecursion
	 *            States the current number of recursions. Upon calling this method, the value should always be 0.
	 * @return A new evaluation result that contains the result of the evaluation.
	 */
	Collection<IEvaluationResult<VALUE>> evaluate(final STATE currentState, final int currentRecursion);

	/**
	 * Computes the inverse of {@link #evaluate(IAbstractState)} relative to some result of
	 * {@link #evaluate(IAbstractState)}.
	 *
	 * TODO: Explain application of inverseEvaluate better
	 *
	 * @param evalResult
	 *            The result of an earlier application of evaluate to <code>state</code>.
	 * @param state
	 *            The state on which the inverseEvaluation should be applied.
	 * @param currentRecursion
	 *            States the current number of recursions. Upon calling this method, the value should always be 0.
	 * @return The result of the inverse application of the evaluate function.
	 */
	Collection<STATE> inverseEvaluate(final IEvaluationResult<VALUE> evalResult, final STATE state,
			final int currentRecursion);

	/**
	 * Adds a sub-evaluator to the evaluator.
	 *
	 * @param evaluator
	 *            The evaluator to add.
	 */
	void addSubEvaluator(final IEvaluator<VALUE, STATE> evaluator);

	/**
	 * @return <code>true</code> if and only if there are still free sub evaluators. <code>false</code> otherwise.
	 */
	boolean hasFreeOperands();

	/**
	 * States whether somewhere in the evaluator occurs a boolean value. This is needed to determine if the boolean
	 * value should be used instead of the returned abstract value. Note: This is needed in the handling of logical
	 * operators in evaluators and is only valid, if there exists 0 or 1 variable identifier in each subtree of the
	 * evaluator.
	 *
	 * @return <code>true</code> if and only if in the sub-tree is a boolean literal or interpretation present,
	 *         <code>false</code> otherwise.
	 */
	boolean containsBool();

	/**
	 * @return The type of the evaluator, according to {@link EvaluatorType}s.
	 */
	EvaluatorType getType();
}
