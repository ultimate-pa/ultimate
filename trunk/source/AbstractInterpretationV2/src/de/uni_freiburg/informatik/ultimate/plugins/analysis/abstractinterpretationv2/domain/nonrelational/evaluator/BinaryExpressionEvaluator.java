package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue.Value;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class BinaryExpressionEvaluator<VALUE extends INonrelationalValue<VALUE>, STATE extends IAbstractState<STATE, CodeBlock>>
        implements INAryEvaluator<VALUE, STATE, CodeBlock> {

	private final Set<IBoogieVar> mVariableSet;
	private final ILogger mLogger;
	private final EvaluatorType mEvaluatorType;
	private final int mMaxParallelSates;

	private final INonrelationalValueFactory<VALUE> mNonrelationalValueFactory;

	private IEvaluator<VALUE, STATE, CodeBlock> mLeftSubEvaluator;
	private IEvaluator<VALUE, STATE, CodeBlock> mRightSubEvaluator;

	private Operator mOperator;

	protected BinaryExpressionEvaluator(final ILogger logger, final EvaluatorType type, final int maxParallelStates,
	        final INonrelationalValueFactory<VALUE> nonrelationalValueFactory) {
		mLogger = logger;
		mVariableSet = new HashSet<>();
		mEvaluatorType = type;
		mMaxParallelSates = maxParallelStates;
		mNonrelationalValueFactory = nonrelationalValueFactory;
	}

	@Override
	public List<IEvaluationResult<VALUE>> evaluate(STATE currentState) {
		assert currentState != null;

		final List<IEvaluationResult<VALUE>> returnList = new ArrayList<>();

		final List<IEvaluationResult<VALUE>> firstResult = mLeftSubEvaluator.evaluate(currentState);
		final List<IEvaluationResult<VALUE>> secondResult = mRightSubEvaluator.evaluate(currentState);

		mLeftSubEvaluator.getVarIdentifiers().forEach(var -> mVariableSet.add(var));
		mRightSubEvaluator.getVarIdentifiers().forEach(var -> mVariableSet.add(var));

		for (final IEvaluationResult<VALUE> res1 : firstResult) {
			for (final IEvaluationResult<VALUE> res2 : secondResult) {
				VALUE returnValue = mNonrelationalValueFactory.ceateTopValue();
				BooleanValue returnBool = new BooleanValue();

				switch (mOperator) {
				case ARITHPLUS:
					returnValue = res1.getValue().add(res2.getValue());
					returnBool = new BooleanValue(false);
					break;
				case ARITHMINUS:
					returnValue = res1.getValue().subtract(res2.getValue());
					returnBool = new BooleanValue(false);
					break;
				case ARITHMUL:
					returnValue = res1.getValue().multiply(res2.getValue());
					returnBool = new BooleanValue(false);
					break;
				case ARITHDIV:
					switch (mEvaluatorType) {
					case INTEGER:
						returnValue = res1.getValue().integerDivide(res2.getValue());
						break;
					case REAL:
						returnValue = res1.getValue().divide(res2.getValue());
						break;
					default:
						throw new UnsupportedOperationException(
						        "Division on types other than integers and reals is undefined.");
					}
					returnBool = new BooleanValue(false);
					break;
				case ARITHMOD:
					switch (mEvaluatorType) {
					case INTEGER:
						returnValue = res1.getValue().modulo(res2.getValue(), true);
						break;
					case REAL:
						returnValue = res1.getValue().modulo(res2.getValue(), false);
						break;
					default:
						throw new UnsupportedOperationException(
						        "Modulo operation on types other than integers and reals is undefined.");
					}
					returnBool = new BooleanValue(false);
					break;
				case LOGICAND:
					returnBool = res1.getBooleanValue().and(res2.getBooleanValue());
					break;
				case LOGICOR:
					returnBool = res1.getBooleanValue().or(res2.getBooleanValue());
					break;
				case LOGICIMPLIES:
					throw new UnsupportedOperationException(
					        "Implications should have been removed during expression normalization.");
				case LOGICIFF:
					throw new UnsupportedOperationException(
					        "If and only if expressions should have been removed during expression normalization.");
				case COMPEQ:
					if (mLeftSubEvaluator.containsBool() || mRightSubEvaluator.containsBool()) {
						returnBool = ((res1.getBooleanValue().intersect(res2.getBooleanValue()))
						        .getValue() != Value.BOTTOM ? new BooleanValue(true) : new BooleanValue(Value.BOTTOM));
					}

					returnValue = res1.getValue().intersect(res2.getValue());

					if (returnBool.isBottom() || returnValue.isBottom()) {
						returnBool = new BooleanValue(false);
						break;
					}

					if (!mLeftSubEvaluator.containsBool() && !mRightSubEvaluator.containsBool()) {
						if (returnValue.isEqualTo(res1.getValue()) && returnValue.isEqualTo(res2.getValue())) {
							returnBool = new BooleanValue(true);
						} else {
							returnBool = new BooleanValue();
						}
					}
					break;
				case COMPNEQ:
					throw new UnsupportedOperationException(
					        "Not equals expressions should have been removed during expression normalization.");
				case COMPGT:
					returnValue = res1.getValue().greaterThan(res2.getValue());
					
					if (returnValue.isBottom()) {
						returnBool = new BooleanValue(false);
					} else {
						returnBool = res1.getValue().isGreaterThan(res2.getValue());
					}
					break;
					// TODO: create interface method for LessThan in intervals as well.
					mLogger.warn(
					        "Cannot handle greater than operators precisely. Using greater or equal over-approximation instead.");
				case COMPGEQ:
					returnValue = res1.getValue().greaterOrEqual(res2.getValue());
					
					if (returnValue.isBottom()) {
						returnBool = new BooleanValue(false);
					} else {
						returnBool = res1.getValue().isLessOrEqual(res2.getValue());
						// TODO: Interval: Move less or equal handling from binary exp. eval. to interval domain value!
					}
					break;
				case COMPLT:
					
				}
			}
		}
		return null;
	}

	@Override
	public List<STATE> inverseEvaluate(IEvaluationResult<VALUE> computedValue, STATE currentState) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void addSubEvaluator(IEvaluator<VALUE, STATE, CodeBlock> evaluator) {
		// TODO Auto-generated method stub

	}

	@Override
	public Set<IBoogieVar> getVarIdentifiers() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean hasFreeOperands() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean containsBool() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void setOperator(Object operator) {
		// TODO Auto-generated method stub

	}

	@Override
	public int getArity() {
		// TODO Auto-generated method stub
		return 0;
	}

}
