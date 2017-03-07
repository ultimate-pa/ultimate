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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;

public class ApplicationTermEvaluator<VALUE, STATE extends IAbstractState<STATE, VARDECL>, VARDECL>
		implements INaryTermEvaluator<VALUE, STATE, VARDECL> {
	
	private final int mArity;
	private final List<ITermEvaluator<VALUE, STATE, VARDECL>> mSubEvaluators;
	private final String mOperator;
	private final Supplier<STATE> mBottomStateSupplier;

	private static final String TRUE = "true";
	private static final String FALSE = "false";
	
	protected ApplicationTermEvaluator(final int arity, final String operator,
			final Supplier<STATE> bottomStateSupplier) {
		mArity = arity;
		mSubEvaluators = new ArrayList<>();
		mOperator = operator;
		mBottomStateSupplier = bottomStateSupplier;
	}

	@Override
	public List<IEvaluationResult<VALUE>> evaluate(final STATE currentState) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public List<STATE> inverseEvaluate(final IEvaluationResult<VALUE> evaluationResult, final STATE state) {
		if (mOperator == TRUE) {
			return Collections.singletonList(state);
		} else if (mOperator == FALSE) {
			return Collections.singletonList(mBottomStateSupplier.get());
		}

		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public void addSubEvaluator(final ITermEvaluator<VALUE, STATE, VARDECL> evaluator) {
		if (mSubEvaluators.size() >= mArity) {
			throw new UnsupportedOperationException(
					"The arity of this evaluator (" + mArity + ") does not allow to add additional sub evaluators.");
		}
		mSubEvaluators.add(evaluator);
	}
	
	@Override
	public boolean hasFreeOperands() {
		return mSubEvaluators.size() < mArity;
	}
	
	@Override
	public boolean containsBool() {
		if (mArity == 0) {
			if (mOperator.equals(TRUE) || mOperator.equals(FALSE)) {
				return true;
			}
			throw new UnsupportedOperationException(
					"An arity of 0 should indicate containment of boolean values, however, the operator was "
							+ "unsupported or not boolean: " + mOperator);
		}
		return mSubEvaluators.stream().anyMatch(eval -> eval.containsBool());

	}
	
	@Override
	public Set<String> getVarIdentifiers() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int getArity() {
		return mArity;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append("(");
		sb.append(mOperator);
		sb.append(" ");
		sb.append(mSubEvaluators.stream().map(sub -> sub.toString()).collect(Collectors.joining(" ")));
		sb.append(")");

		return sb.toString();
	}

}
