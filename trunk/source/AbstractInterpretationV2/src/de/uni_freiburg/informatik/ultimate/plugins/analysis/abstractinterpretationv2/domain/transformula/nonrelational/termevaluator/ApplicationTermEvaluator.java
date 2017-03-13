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
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;

public class ApplicationTermEvaluator<VALUE extends INonrelationalValue<VALUE>, STATE extends IAbstractState<STATE, VARDECL>, VARDECL>
		implements INaryTermEvaluator<VALUE, STATE, VARDECL> {
	
	private final int mArity;
	private final List<ITermEvaluator<VALUE, STATE, VARDECL>> mSubEvaluators;
	private final String mOperator;
	private final INonrelationalValueFactory<VALUE> mNonrelationalValueFactory;
	private final Supplier<STATE> mBottomStateSupplier;
	private final VALUE mTopValue;
	private final int mMaxParallelStates;
	private final Set<String> mVarIdentifiers;

	private static final String TRUE = "true";
	private static final String FALSE = "false";
	private static final String COMPEQ = "=";
	
	protected ApplicationTermEvaluator(final int arity, final String operator, final int maxParallelStates,
			final INonrelationalValueFactory<VALUE> nonrelationalValueFactory,
			final Supplier<STATE> bottomStateSupplier) {
		mArity = arity;
		mSubEvaluators = new ArrayList<>();
		mOperator = operator;
		mNonrelationalValueFactory = nonrelationalValueFactory;
		mMaxParallelStates = maxParallelStates;
		mBottomStateSupplier = bottomStateSupplier;
		mTopValue = mNonrelationalValueFactory.createTopValue();
		mVarIdentifiers = new HashSet<>();
	}

	@Override
	public List<IEvaluationResult<VALUE>> evaluate(final STATE currentState) {
		assert currentState != null;

		if (mOperator == TRUE) {
			return onlyBooleanValue(BooleanValue.TRUE);
		} else if (mOperator == FALSE) {
			return onlyBooleanValue(BooleanValue.FALSE);
		}

		mSubEvaluators.forEach(sub -> mVarIdentifiers.addAll(sub.getVarIdentifiers()));

		final List<List<IEvaluationResult<VALUE>>> subResults = new ArrayList<>();
		mSubEvaluators.forEach(sub -> subResults.add(sub.evaluate(currentState)));

		final List<List<IEvaluationResult<VALUE>>> permuts = generatePermutations(subResults, 0, new ArrayList<>());
		
		// Operator must be applied to all lists in permuts.
		for (final List<IEvaluationResult<VALUE>> permutList : permuts) {
			
			if (mOperator == COMPEQ) {
				return evaluateEquality(permutList);
			}
		}

		// NonrelationalEvaluationResult<VALUE> returnResult = new NonrelationalEvaluationResult<>(value, booleanValue);
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * Constructs all permutations of elements within the input list's lists.
	 *
	 * <p>
	 * For example, if there are two lists in input:<br />
	 * input = [[A, B, C], [1, 2, 3, 4]] <br />
	 * Then the result should be:<br />
	 * result = [[A, 1], [A, 2], [A, 3], [A, 4], [B, 1], [B, 2], [B, 3], [B, 4], [C, 1], [C, 2], [C, 3], [C, 4]]
	 * </p>
	 *
	 * @param input
	 *            The input list of lists.
	 * @param depth
	 *            The current depth.
	 * @param trace
	 *            The current working list
	 * @return An element of the returned list of lists (i.e. a list).
	 */
	private static <VALUE> List<List<VALUE>> generatePermutations(final List<List<VALUE>> input, final int depth,
			final List<VALUE> trace) {
		if (depth == input.size() - 1) {
			final List<List<VALUE>> valueList = new ArrayList<>();
			for (final VALUE last : input.get(input.size() - 1)) {
				final List<VALUE> tmpTrace = new ArrayList<>();
				trace.forEach(elem -> tmpTrace.add(elem));
				tmpTrace.add(last);
				valueList.add(tmpTrace);
			}
			return valueList;
		} else {
			final List<List<VALUE>> returnList = new ArrayList<>();
			for (final VALUE elem : input.get(depth)) {
				final List<VALUE> tmpTrace = new ArrayList<>();
				trace.forEach(str -> tmpTrace.add(str));
				tmpTrace.add(elem);
				returnList.addAll(generatePermutations(input, depth + 1, tmpTrace));
			}
			return returnList;
		}
	}

	private List<IEvaluationResult<VALUE>> onlyBooleanValue(final BooleanValue value) {
		assert value != null;
		assert value != BooleanValue.INVALID;
		return Collections.singletonList(new NonrelationalEvaluationResult<>(mTopValue, value));
	}
	
	private List<IEvaluationResult<VALUE>> evaluateEquality(final List<IEvaluationResult<VALUE>> arguments) {
		assert arguments != null;

		if (arguments.size() < 2) {
			throw new UnsupportedOperationException("The evaluation result list (" + arguments
					+ ") does not contain the necessary number of arguments to check for equality.");
		}

		BooleanValue returnBool = BooleanValue.INVALID;
		if (mSubEvaluators.stream().anyMatch(sub -> sub.containsBool())) {
			arguments.get(0).getBooleanValue();
			// Apply intersection to every element in the arguments list and check whether the result not bottom.
			// It the result is bottom, returnBool becomes bottom; otherwise, returnBool becomes true.
			returnBool = arguments.stream().map(elem -> elem.getBooleanValue()).reduce(BooleanValue.TOP,
					(a, b) -> (a.intersect(b))) != BooleanValue.BOTTOM ? BooleanValue.TRUE : BooleanValue.BOTTOM;
		}
		
		final VALUE returnValue = arguments.stream().map(elem -> elem.getValue())
				.reduce(mNonrelationalValueFactory.createTopValue(), (a, b) -> a.intersect(b));
		
		if (returnBool.isBottom() || returnValue.isBottom()) {
			returnBool = BooleanValue.FALSE;
		} else if (!mSubEvaluators.stream().anyMatch(sub -> sub.containsBool())) {
			returnBool = BooleanValue.TOP;
			for (int i = 1; i < arguments.size(); i++) {
				final VALUE val1 = arguments.get(i - 1).getValue();
				final VALUE val2 = arguments.get(i).getValue();
				returnBool = returnBool.intersect(val1.compareEquality(val2));
			}
		}
		return Collections.singletonList(new NonrelationalEvaluationResult<>(returnValue, returnBool));
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
		return mVarIdentifiers;
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
