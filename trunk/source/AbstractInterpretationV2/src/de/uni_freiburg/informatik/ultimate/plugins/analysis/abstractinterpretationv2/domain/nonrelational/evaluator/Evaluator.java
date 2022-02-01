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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;

/**
 * Default interface for an expression evaluator. Each Evaluator should implement this interface in order to allow for
 * expressions to be evaluated.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <VALUE>
 *            The value type of the abstract domain.
 * @param <ACTION>
 *            Any action type.
 * @param <VARDECL>
 *            Any variable declaration type.
 */
public abstract class Evaluator<VALUE extends INonrelationalValue<VALUE>, STATE extends IAbstractState<STATE>> {

	private final int mMaxRecursionDepth;
	private final VALUE mTopValue;
	private final List<Evaluator<VALUE, STATE>> mSubEvaluators;

	private int mCurrentEvaluationRecursion;
	private int mCurrentInverseEvaluationRecursion;
	private final EvaluatorLogger mLogger;

	public Evaluator(final int maxRecursionDepth, final INonrelationalValueFactory<VALUE> nonrelationalValueFactory,
			final EvaluatorLogger logger) {
		mLogger = logger;
		mMaxRecursionDepth = maxRecursionDepth;
		mCurrentEvaluationRecursion = -1;
		mCurrentInverseEvaluationRecursion = -1;
		mTopValue = nonrelationalValueFactory.createTopValue();
		mSubEvaluators = new ArrayList<>();
	}

	/**
	 * Evaluates the evaluator with all its sub-evaluators according to the given state while tracking recursions.
	 *
	 * @param currentState
	 *            The originating state to evaluate from.
	 * @param currentRecursion
	 *            States the current number of recursions. Upon calling this method, the value should always be 0.
	 * @return A new evaluation result that contains the result of the evaluation.
	 */
	public final Collection<IEvaluationResult<VALUE>> evaluate(final STATE currentState, final int currentRecursion) {

		if (mMaxRecursionDepth >= 0 && currentRecursion > mMaxRecursionDepth) {
			return Collections.singletonList(new NonrelationalEvaluationResult<>(mTopValue, BooleanValue.TOP));
		}

		if (mCurrentEvaluationRecursion < currentRecursion) {
			mCurrentEvaluationRecursion = currentRecursion;
		}

		return evaluate(currentState);
	}

	/**
	 * Evaluates the evaluator with all its sub-evaluators according to the given state.
	 *
	 * @param currentState
	 *            The originating state to evaluate from.
	 * @return A new evaluation result that contains the result of the evaluation.
	 */
	protected abstract Collection<IEvaluationResult<VALUE>> evaluate(final STATE currentState);

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
	 * @return The result of the inverse application of the evaluate function.
	 */
	public final Collection<STATE> inverseEvaluate(final IEvaluationResult<VALUE> evalResult, final STATE oldstate,
			final int currentRecursion) {
		if (mMaxRecursionDepth >= 0 && currentRecursion > mMaxRecursionDepth) {
			return Collections.singletonList(oldstate);
		}

		if (mCurrentInverseEvaluationRecursion < currentRecursion) {
			mCurrentInverseEvaluationRecursion = currentRecursion;
		}
		// mLogger.getLogger().info(
		// String.format("Inverse evaluation in depth %s for state %s", currentRecursion, oldstate.hashCode()));
		return inverseEvaluate(evalResult, oldstate);
	}

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
	 * @return The result of the inverse application of the evaluate function.
	 */
	protected abstract Collection<STATE> inverseEvaluate(final IEvaluationResult<VALUE> evalResult, final STATE state);

	/**
	 * Adds a sub-evaluator to the evaluator.
	 *
	 * @param evaluator
	 *            The evaluator to add.
	 */
	public final void addSubEvaluator(final Evaluator<VALUE, STATE> evaluator) {
		assert evaluator != null;

		if (!hasFreeOperands()) {
			throw new UnsupportedOperationException("There are no free sub evaluators left to be assigned to.");
		}

		mSubEvaluators.add(evaluator);
	}

	/**
	 * @return <code>true</code> if and only if there are still free sub evaluators. <code>false</code> otherwise.
	 */
	public abstract boolean hasFreeOperands();

	/**
	 * States whether somewhere in the evaluator occurs a boolean value. This is needed to determine if the boolean
	 * value should be used instead of the returned abstract value. Note: This is needed in the handling of logical
	 * operators in evaluators and is only valid, if there exists 0 or 1 variable identifier in each subtree of the
	 * evaluator.
	 *
	 * @return <code>true</code> if and only if in the sub-tree is a boolean literal or interpretation present,
	 *         <code>false</code> otherwise.
	 */
	public abstract boolean containsBool();

	/**
	 * @return The type of the evaluator, according to {@link EvaluatorType}s.
	 */
	public abstract EvaluatorType getType();

	/**
	 * @return The current recursion depth value of this evaluator during evaluation.
	 */
	protected final int getCurrentEvaluationRecursion() {
		return mCurrentEvaluationRecursion;
	}

	/**
	 * @return The current recursion depth value of this evaluator during inverse evaluation.
	 */
	protected final int getCurrentInverseEvaluationRecursion() {
		return mCurrentInverseEvaluationRecursion;
	}

	/**
	 * Returns a sub evaluator for a given index.
	 *
	 * @param index
	 *            The index of the sub evaluator.
	 * @return The sub evaluator with requested index.
	 */
	protected final Evaluator<VALUE, STATE> getSubEvaluator(final int index) {
		if (index < 0 || index >= mSubEvaluators.size()) {
			throw new UnsupportedOperationException("No evaluator with index " + index + " present.");
		}

		return mSubEvaluators.get(index);
	}

	/**
	 * @return The number of assigned sub evaluators.
	 */
	protected final int getNumberOfSubEvaluators() {
		return mSubEvaluators.size();
	}

	/**
	 * @return The sum of the maximum recursion depth of all sub evaluators and the current recursion depth.
	 */
	public final int getEvaluationRecursionDepth() {
		return Math.max(mCurrentEvaluationRecursion,
				mSubEvaluators.stream().mapToInt(Evaluator::getEvaluationRecursionDepth).max().orElse(0));
	}

	/**
	 * @return The sum of the maximum recursion depth of all sub inverse evaluators and the current recursion depth.
	 */
	public final int getInverseEvaluationRecursionDepth() {
		return Math.max(mCurrentInverseEvaluationRecursion,
				mSubEvaluators.stream().mapToInt(Evaluator::getInverseEvaluationRecursionDepth).max().orElse(0));
	}

}
