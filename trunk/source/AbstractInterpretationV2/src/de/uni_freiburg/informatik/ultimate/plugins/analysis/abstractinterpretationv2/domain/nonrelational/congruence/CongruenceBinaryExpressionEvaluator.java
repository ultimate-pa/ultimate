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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * 
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */

public class CongruenceBinaryExpressionEvaluator
        implements INAryEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> {

	private final Set<String> mVariableSet;
	private final Logger mLogger;
	private final int mMaxParallelStates;

	private IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> mLeftSubEvaluator;
	private IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> mRightSubEvaluator;

	private Operator mOperator;
	
	private CongruenceDomainValue mModul = null;
	private CongruenceDomainValue mRest = null;

	protected CongruenceBinaryExpressionEvaluator(final Logger logger, final EvaluatorType type) {
		mLogger = logger;
		mVariableSet = new HashSet<>();
		mMaxParallelStates = new UltimatePreferenceStore(Activator.PLUGIN_ID)
		        .getInt(AbsIntPrefInitializer.LABEL_STATES_UNTIL_MERGE);
	}

	@Override
	public List<IEvaluationResult<CongruenceDomainValue>> evaluate(CongruenceDomainState currentState) {

		final List<IEvaluationResult<CongruenceDomainValue>> returnList = new ArrayList<>();

		assert currentState != null;

		final List<IEvaluationResult<CongruenceDomainValue>> firstResult = mLeftSubEvaluator.evaluate(currentState);
		final List<IEvaluationResult<CongruenceDomainValue>> secondResult = mRightSubEvaluator.evaluate(currentState);

		for (String var : mLeftSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}
		for (String var : mRightSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}

		for (final IEvaluationResult<CongruenceDomainValue> res1 : firstResult) {
			for (final IEvaluationResult<CongruenceDomainValue> res2 : secondResult) {
				CongruenceDomainValue returnValue = new CongruenceDomainValue();
				BooleanValue returnBool = new BooleanValue();
				
				CongruenceDomainValue v1 = res1.getValue();
				CongruenceDomainValue v2 = res2.getValue();

				switch (mOperator) {
				case ARITHPLUS:
					returnValue = v1.add(v2);
					returnBool = new BooleanValue(false);
					break;
				case ARITHMINUS:
					returnValue = v1.subtract(v2);
					returnBool = new BooleanValue(false);
					break;
				case ARITHMUL:
					returnValue = v1.multiply(v2);
					returnBool = new BooleanValue(false);
					break;
				case ARITHDIV:
					returnValue = v1.divide(v2);
					returnBool = new BooleanValue(false);
					break;
				case ARITHMOD:
					returnValue = v1.mod(v2);
					returnBool = new BooleanValue(false);
					mModul = v2;
					break;
				case LOGICAND:
					returnBool = res1.getBooleanValue().and(res2.getBooleanValue());
					break;
				case LOGICOR:
					returnBool = res1.getBooleanValue().or(res2.getBooleanValue());
					break;
				case LOGICIMPLIES:
					throw new UnsupportedOperationException("Implications should have been resolved earlier.");
				case LOGICIFF:
					throw new UnsupportedOperationException(
					        "If and only if expressions should have been resolved earlier.");
				case COMPEQ:
					if (mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool()) {
						returnBool = res1.getBooleanValue().intersect(res2.getBooleanValue());
					}

					returnValue = v1.intersect(v2);

					if (returnBool.isBottom() || returnValue.isBottom()) {
						returnBool = new BooleanValue(false);
						break;
					}
					
					if (mLeftSubEvaluator instanceof CongruenceBinaryExpressionEvaluator) {
						CongruenceBinaryExpressionEvaluator sub  = (CongruenceBinaryExpressionEvaluator) mLeftSubEvaluator;
						if (sub.mOperator == Operator.ARITHMOD) {
							if (v2.isConstant()) {
								if (v2.value().signum() < 0 || sub.mModul.isConstant() && v2.value().compareTo(sub.mModul.value().abs()) >= 0) {
									returnBool = new BooleanValue(false);
									break;
								}
							}
						}
					}
					
					if (mRightSubEvaluator instanceof CongruenceBinaryExpressionEvaluator) {
						CongruenceBinaryExpressionEvaluator sub  = (CongruenceBinaryExpressionEvaluator) mRightSubEvaluator;
						if (sub.mOperator == Operator.ARITHMOD) {
							if (v1.isConstant()) {
								if (v1.value().signum() < 0 || sub.mModul.isConstant() && v1.value().compareTo(sub.mModul.value().abs()) >= 0) {
									returnBool = new BooleanValue(false);
									break;
								}
							}
						}
					}

					if (!mLeftSubEvaluator.containsBool() && !mRightSubEvaluator.containsBool()) {
						if (v1.isConstant() && v2.isConstant()) {
							returnBool = new BooleanValue(v1.value().equals(v2.value()));
							break;
						}
						if (returnValue.isBottom()) {
							returnBool = new BooleanValue(false);
						} else {
							returnBool = new BooleanValue();
						}
					}
					break;
				case COMPNEQ:
					if (v1.isConstant() && v2.isConstant()) {
						returnBool = new BooleanValue(!v1.value().equals(v2.value()));
					}
					break;
				case COMPGT:
					if (v1.isConstant() && v2.isConstant()) {
						returnBool = new BooleanValue(v1.value().compareTo(v2.value()) > 0);
					}
					break;
				case COMPGEQ:
					if (v1.isConstant() && v2.isConstant()) {
						returnBool = new BooleanValue(v1.value().compareTo(v2.value()) >= 0);
					}
					break;
				case COMPLT:
					if (v1.isConstant() && v2.isConstant()) {
						returnBool = new BooleanValue(v1.value().compareTo(v2.value()) < 0);
					}
					break;
				case COMPLEQ:
					if (v1.isConstant() && v2.isConstant()) {
						returnBool = new BooleanValue(v1.value().compareTo(v2.value()) <= 0);
					}
					break;
				case COMPPO:
				default:
					returnBool = new BooleanValue(false);
					mLogger.warn("Possible loss of precision: cannot handle operator " + mOperator
					        + ". Returning current state.");
					returnValue = new CongruenceDomainValue();
				}
				returnList.add(new CongruenceDomainEvaluationResult(returnValue, returnBool));
			}
		}

		assert returnList.size() != 0;
		return CongruenceUtils.mergeIfNecessary(returnList, mMaxParallelStates);

	}

	@Override
	public boolean containsBool() {
		return mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool();
	}

	@Override
	public void addSubEvaluator(IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> evaluator) {
		assert evaluator != null;

		if (mLeftSubEvaluator != null && mRightSubEvaluator != null) {
			throw new UnsupportedOperationException("There are no free sub evaluators left to be assigned.");
		}

		if (mLeftSubEvaluator == null) {
			mLeftSubEvaluator = evaluator;
			return;
		}

		mRightSubEvaluator = evaluator;
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return mVariableSet;
	}

	@Override
	public boolean hasFreeOperands() {
		return (mLeftSubEvaluator == null || mRightSubEvaluator == null);
	}

	@Override
	public void setOperator(Object operator) {
		assert operator != null;
		assert operator instanceof Operator;

		mOperator = (Operator) operator;
	}

	@Override
	public int getArity() {
		return 2;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append(mLeftSubEvaluator);

		switch (mOperator) {
		case ARITHDIV:
			sb.append(" / ");
			break;
		case ARITHMINUS:
			sb.append(" - ");
			break;
		case ARITHMOD:
			sb.append(" % ");
			break;
		case ARITHMUL:
			sb.append(" * ");
			break;
		case ARITHPLUS:
			sb.append(" + ");
			break;
		case COMPEQ:
			sb.append(" == ");
			break;
		case COMPGEQ:
			sb.append(" >= ");
			break;
		case COMPGT:
			sb.append(" > ");
			break;
		case COMPLEQ:
			sb.append(" <= ");
			break;
		case COMPLT:
			sb.append(" < ");
			break;
		case COMPNEQ:
			sb.append(" != ");
			break;
		case LOGICAND:
			sb.append(" && ");
			break;
		case LOGICIFF:
			sb.append(" <==> ");
			break;
		case LOGICIMPLIES:
			sb.append(" ==> ");
			break;
		case LOGICOR:
			sb.append(" || ");
			break;
		default:
			mOperator.name();
		}

		sb.append(mRightSubEvaluator);

		return sb.toString();
	}

	@Override
	public List<CongruenceDomainState> inverseEvaluate(final IEvaluationResult<CongruenceDomainValue> computedValue,
	        final CongruenceDomainState currentState) {

		final List<CongruenceDomainState> returnList = new ArrayList<>();

		final CongruenceDomainValue referenceValue = computedValue.getValue();
		final BooleanValue referenceBool = computedValue.getBooleanValue();

		final List<IEvaluationResult<CongruenceDomainValue>> leftValue = mLeftSubEvaluator.evaluate(currentState);
		final List<IEvaluationResult<CongruenceDomainValue>> rightValue = mRightSubEvaluator.evaluate(currentState);

		for (final IEvaluationResult<CongruenceDomainValue> left : leftValue) {
			for (final IEvaluationResult<CongruenceDomainValue> right : rightValue) {
				List<CongruenceDomainState> returnStates = new ArrayList<>();

				switch (mOperator) {
				case LOGICAND:
					final List<CongruenceDomainState> leftAnd = mLeftSubEvaluator.inverseEvaluate(computedValue,
					        currentState);
					final List<CongruenceDomainState> rightAnd = mRightSubEvaluator.inverseEvaluate(computedValue,
					        currentState);
					for (final CongruenceDomainState le : leftAnd) {
						for (final CongruenceDomainState ri : rightAnd) {
							returnStates.add(le.intersect(ri));
						}
					}
					break;
				case LOGICOR:
					final List<CongruenceDomainState> leftOr = mLeftSubEvaluator.inverseEvaluate(computedValue,
					        currentState);
					final List<CongruenceDomainState> rightOr = mRightSubEvaluator.inverseEvaluate(computedValue,
					        currentState);
					for (final CongruenceDomainState le : leftOr) {
						returnStates.add(le);
					}
					for (final CongruenceDomainState ri : rightOr) {
						returnStates.add(ri);
					}
					break;
				case LOGICIMPLIES:
					throw new UnsupportedOperationException("Implications should have been resolved earlier.");
				case LOGICIFF:
					throw new UnsupportedOperationException(
					        "If and only if expressions should have been resolved earlier.");
				case COMPEQ:
					final CongruenceDomainValue newLeft = computeNewValue(referenceValue, left.getValue(),
					        right.getValue(), true);
					final CongruenceDomainValue newRight = computeNewValue(referenceValue, right.getValue(),
					        left.getValue(), false);

					final CongruenceDomainEvaluationResult leftEvalresult = new CongruenceDomainEvaluationResult(newLeft,
					        referenceBool);
					final CongruenceDomainEvaluationResult rightEvalresult = new CongruenceDomainEvaluationResult(newRight,
					        referenceBool);
					
					if (mLeftSubEvaluator instanceof CongruenceBinaryExpressionEvaluator) {
						CongruenceBinaryExpressionEvaluator c = (CongruenceBinaryExpressionEvaluator) mLeftSubEvaluator;
						c.mRest = rightEvalresult.getValue();
					}
					
					if (mRightSubEvaluator instanceof CongruenceBinaryExpressionEvaluator) {
						CongruenceBinaryExpressionEvaluator c = (CongruenceBinaryExpressionEvaluator) mRightSubEvaluator;
						c.mRest = leftEvalresult.getValue();
					}

					final List<CongruenceDomainState> leftEq = mLeftSubEvaluator.inverseEvaluate(leftEvalresult,
					        currentState);
					final List<CongruenceDomainState> rightEq = mRightSubEvaluator.inverseEvaluate(rightEvalresult,
					        currentState);
					for (final CongruenceDomainState le : leftEq) {
						for (final CongruenceDomainState ri : rightEq) {
							returnStates.add(le.intersect(ri));
						}
					}
					break;
				case ARITHDIV:
				case ARITHMINUS:
				case ARITHMOD:
				case ARITHMUL:
				case ARITHPLUS:
					final CongruenceDomainValue newArithValueLeft = computeNewValue(referenceValue, left.getValue(),
					        right.getValue(), true);
					final CongruenceDomainValue newArithValueRight = computeNewValue(referenceValue, right.getValue(),
					        left.getValue(), false);

					final CongruenceDomainEvaluationResult inverseResultArithLeft = new CongruenceDomainEvaluationResult(
					        newArithValueLeft, referenceBool);
					final CongruenceDomainEvaluationResult inverseResultArithRight = new CongruenceDomainEvaluationResult(
					        newArithValueRight, referenceBool);

					final List<CongruenceDomainState> leftInverseArith = mLeftSubEvaluator
					        .inverseEvaluate(inverseResultArithLeft, currentState);
					final List<CongruenceDomainState> rightInverseArith = mRightSubEvaluator
					        .inverseEvaluate(inverseResultArithRight, currentState);
					
					for (final CongruenceDomainState le : leftInverseArith) {
						for (final CongruenceDomainState ri : rightInverseArith) {
							returnStates.add(le.intersect(ri));
						}
					}
					break;
				default:
					returnStates.add(currentState);
					break;

				}

				if (returnStates.size() == 0) {
					returnStates.add(currentState);
				}

				returnList.addAll(returnStates);
			}
		}

		assert returnList.size() != 0;
		return returnList;
	}

	private CongruenceDomainValue computeNewValue(final CongruenceDomainValue referenceValue,
	        final CongruenceDomainValue oldValue, final CongruenceDomainValue otherValue, boolean left) {
		CongruenceDomainValue newValue;

		switch (mOperator) {
		case ARITHPLUS:
			newValue = referenceValue.subtract(otherValue);
			newValue = newValue.intersect(oldValue);
			break;
		case ARITHMINUS:
			if (left) {
				newValue = referenceValue.add(otherValue);
			} else {
				newValue = otherValue.subtract(referenceValue);
			}
			newValue = newValue.intersect(oldValue);
			break;
		case ARITHMUL:
			newValue = referenceValue.divide(otherValue);
			newValue = newValue.intersect(oldValue);
			break;
		case ARITHDIV:
			if (left) {
				newValue = referenceValue.multiply(otherValue);
			} else {
				newValue = otherValue.divide(referenceValue);
			}
			newValue = newValue.intersect(oldValue);
			break;
		case ARITHMOD:
			if (left && mRest != null) {
				newValue = oldValue.modEquals(otherValue, mRest);
			} else {
				newValue = oldValue;
			}
			break;
		case COMPEQ:
		case COMPLEQ:
		case COMPLT:
		case COMPGEQ:
		case COMPGT:
		case COMPNEQ:
			newValue = referenceValue;
			break;
		default:
			throw new UnsupportedOperationException("Not implemented: " + mOperator);
		}
		return newValue;
	}
}
