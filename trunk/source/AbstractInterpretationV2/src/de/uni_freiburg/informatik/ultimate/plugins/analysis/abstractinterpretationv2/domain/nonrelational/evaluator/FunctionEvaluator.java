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
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;

/**
 * Represents an Evaluator for a function symbol. Note that currently, this evaluator always returns &top; as the
 * evaluation result and always the old state as the inverse evaluation result.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <VALUE>
 * @param <STATE>
 */
public class FunctionEvaluator<VALUE extends INonrelationalValue<VALUE>, STATE extends IAbstractState<STATE>>
		extends Evaluator<VALUE, STATE> {

	private final String mName;
	private final int mInParamCount;
	private final INonrelationalValueFactory<VALUE> mNonrelationalValueFactory;

	private final EvaluatorType mType;

	public FunctionEvaluator(final String name, final int numInParams, final int maxRecursionDepth,
			final INonrelationalValueFactory<VALUE> nonrelationalValueFactory, final EvaluatorType type,
			final EvaluatorLogger logger) {
		super(maxRecursionDepth, nonrelationalValueFactory, logger);
		mName = name;
		mInParamCount = numInParams;
		mNonrelationalValueFactory = nonrelationalValueFactory;
		mType = type;
	}

	@Override
	public Collection<IEvaluationResult<VALUE>> evaluate(final STATE currentState) {
		assert currentState != null;

		// Return a top value since functions cannot be handled, yet.
		return Collections.singletonList(
				new NonrelationalEvaluationResult<>(mNonrelationalValueFactory.createTopValue(), BooleanValue.TOP));
	}

	@Override
	public Collection<STATE> inverseEvaluate(final IEvaluationResult<VALUE> computedValue, final STATE currentState) {
		assert currentState != null;
		return Collections.singletonList(currentState);
	}

	@Override
	public boolean hasFreeOperands() {
		return getNumberOfSubEvaluators() < mInParamCount;
	}

	@Override
	public boolean containsBool() {
		return false;
	}

	/**
	 * @return The number of in-parameters for this function.
	 */
	public int getNumberOfInParams() {
		return mInParamCount;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append(mName).append('(');
		for (int i = 0; i < getNumberOfSubEvaluators(); i++) {
			if (i > 0) {
				sb.append(", ");
			}
			sb.append(getSubEvaluator(i));
		}
		sb.append(')');

		return sb.toString();
	}

	@Override
	public EvaluatorType getType() {
		return mType;
	}
}
