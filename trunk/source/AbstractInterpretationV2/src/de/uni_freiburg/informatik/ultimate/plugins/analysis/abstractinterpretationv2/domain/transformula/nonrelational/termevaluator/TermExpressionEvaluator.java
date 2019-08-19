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

import java.util.ArrayDeque;
import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;

public class TermExpressionEvaluator<VALUE, STATE extends IAbstractState<STATE>> {

	private final Deque<ITermEvaluator<VALUE, STATE>> mEvaluators;
	private ITermEvaluator<VALUE, STATE> mRootEvaluator;

	/**
	 * The default constructor.
	 */
	public TermExpressionEvaluator() {
		mEvaluators = new ArrayDeque<>();
		mRootEvaluator = null;
	}

	/**
	 * Adds a new {@link ITermEvaluator} to the already existing ones and builds an evaluator tree that defines the
	 * order in which the {@link ITermEvaluator}s should be evaluated. If there is no evaluator present yet, this
	 * function will store the evaluator as the root element which can be retrieved by calling
	 * {@link TermExpressionEvaluator#getRootEvaluator()}.111
	 *
	 * @param evaluator
	 */
	public void addEvaluator(final ITermEvaluator<VALUE, STATE> evaluator) {

		if (mEvaluators.isEmpty()) {
			if (mRootEvaluator != null) {
				throw new IllegalStateException("The root evaluator is not empty. Cannot add new root evaluator.");
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

		// Pop all of the elements that do not have free operands anymore
		while (!mEvaluators.isEmpty()) {
			if (!mEvaluators.peek().hasFreeOperands()) {
				mEvaluators.pop();
			} else {
				break;
			}
		}
	}

	/**
	 * @return The root evaluator of the evaluator tree.
	 */
	public ITermEvaluator<VALUE, STATE> getRootEvaluator() {
		return mRootEvaluator;
	}

	/**
	 * @return <code>true</code> if there are no evaluators present in the {@link TermExpressionEvaluator},
	 *         <code>false</code> otherwise.
	 */
	public boolean isEmpty() {
		return mEvaluators.isEmpty();
	}

	/**
	 * @return <code>true</code> if all evaluators in the {@link TermExpressionEvaluator} are fully built and the
	 *         expression evaluator has a root node, <code>false</code> otherwise.
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
