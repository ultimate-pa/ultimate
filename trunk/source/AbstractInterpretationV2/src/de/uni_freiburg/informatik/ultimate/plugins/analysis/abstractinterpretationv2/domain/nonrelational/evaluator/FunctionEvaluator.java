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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;

public class FunctionEvaluator<VALUE extends INonrelationalValue<VALUE>, STATE extends IAbstractState<STATE>>
		implements IFunctionEvaluator<VALUE, STATE> {

	private final String mName;
	private final int mInParamCount;
	private final INonrelationalValueFactory<VALUE> mNonrelationalValueFactory;

	private final List<IEvaluator<VALUE, STATE>> mInputParamEvaluators;
	private final EvaluatorType mType;

	public FunctionEvaluator(final String name, final int numInParams,
			final INonrelationalValueFactory<VALUE> nonrelationalValueFactory, final EvaluatorType type) {
		mName = name;
		mInParamCount = numInParams;
		mNonrelationalValueFactory = nonrelationalValueFactory;
		mInputParamEvaluators = new ArrayList<>();
		mType = type;
	}

	@Override
	public List<IEvaluationResult<VALUE>> evaluate(final STATE currentState) {
		assert currentState != null;

		final List<IEvaluationResult<VALUE>> returnList = new ArrayList<>();
		final IEvaluationResult<VALUE> res =
				new NonrelationalEvaluationResult<>(mNonrelationalValueFactory.createTopValue(), BooleanValue.TOP);
		returnList.add(res);

		return returnList;
	}

	@Override
	public List<STATE> inverseEvaluate(final IEvaluationResult<VALUE> computedValue, final STATE currentState) {
		assert currentState != null;
		final List<STATE> returnList = new ArrayList<>();
		returnList.add(currentState);
		return returnList;
	}

	@Override
	public void addSubEvaluator(final IEvaluator<VALUE, STATE> evaluator) {
		if (mInputParamEvaluators.size() < mInParamCount) {
			mInputParamEvaluators.add(evaluator);
		} else {
			throw new UnsupportedOperationException("No space left to add sub evaluators to this function evaluator.");
		}
	}

	@Override
	public boolean hasFreeOperands() {
		return mInputParamEvaluators.size() < mInParamCount;
	}

	@Override
	public boolean containsBool() {
		return false;
	}

	@Override
	public int getNumberOfInParams() {
		return mInParamCount;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append(mName).append('(');
		for (int i = 0; i < mInputParamEvaluators.size(); i++) {
			if (i > 0) {
				sb.append(", ");
			}
			sb.append(mInputParamEvaluators.get(i));
		}
		sb.append(')');

		return sb.toString();
	}

	@Override
	public EvaluatorType getType() {
		return mType;
	}

}
