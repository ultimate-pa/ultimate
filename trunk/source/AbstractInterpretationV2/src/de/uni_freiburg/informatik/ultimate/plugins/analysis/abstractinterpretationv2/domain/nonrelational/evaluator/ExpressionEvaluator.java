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

import java.util.ArrayDeque;
import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;

/**
 * Enables the construction and evaluation of multiple {@link IEvaluator}s. It is assumed that the order, in which an
 * abstract syntax tree is traversed to build the different evaluators is pre-order depth-first search where the
 * left-most child element is being evaluated first.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class ExpressionEvaluator<VALUE extends INonrelationalValue<VALUE>, STATE extends IAbstractState<STATE>> {

	private final Deque<Evaluator<VALUE, STATE>> mEvaluators;
	private Evaluator<VALUE, STATE> mRootEvaluator;

	/**
	 * The default constructor.
	 */
	public ExpressionEvaluator() {
		mEvaluators = new ArrayDeque<>();
		mRootEvaluator = null;
	}

	/**
	 * Adds a new {@link IEvaluator} to the already existing ones and builds an evaluator tree that defines the order in
	 * which each {@link IEvaluator} should be evaluated. If there is no evaluator present yet, this function will store
	 * the first evaluator as a root element which can be retrieved by {@link ExpressionEvaluator#getRootEvaluator()}.
	 *
	 * @param evaluator
	 */
	public void addEvaluator(final Evaluator<VALUE, STATE> evaluator) {

		// TODO Insert sanity checks to be on the safe side.

		if (mEvaluators.isEmpty()) {
			if (mRootEvaluator != null) {
				throw new UnsupportedOperationException("The root evaluator is not empty.");
			}

			mEvaluators.push(evaluator);
			mRootEvaluator = evaluator;
		} else {
			if (mEvaluators.peek().hasFreeOperands()) {
				mEvaluators.peek().addSubEvaluator(evaluator);
				if (evaluator.hasFreeOperands()) {
					mEvaluators.push(evaluator);
				}
			}
		}

		// Pop off all the elements that do not have free operands anymore
		while (!mEvaluators.isEmpty()) {
			if (!mEvaluators.peek().hasFreeOperands()) {
				mEvaluators.pop();
			} else {
				break;
			}
		}
	}

	/**
	 * Returns the root evaluator of the evaluation tree.
	 *
	 * @return
	 */
	public Evaluator<VALUE, STATE> getRootEvaluator() {
		return mRootEvaluator;
	}

	/**
	 * Returns <code>true</code> if there are no evaluators present in the {@link ExpressionEvaluator},
	 * <code>false</code> otherwise.
	 *
	 * @return
	 */
	public boolean isEmpty() {
		return mEvaluators.isEmpty();
	}

	/**
	 * Returns <code>true</code> if all added {@link IEvaluator}s have been assembled completely. The root of the
	 * evaluation tree can be obtained via {@link ExpressionEvaluator#getRootEvaluator()}. Returns <code>false</code>
	 * otherwise.
	 *
	 * @return
	 */
	public boolean isFinished() {
		return isEmpty() && (mRootEvaluator != null);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append(mRootEvaluator);

		if (!mEvaluators.isEmpty()) {
			sb.append(", Stack: ").append(mEvaluators);
		}

		return sb.toString();
	}
}
