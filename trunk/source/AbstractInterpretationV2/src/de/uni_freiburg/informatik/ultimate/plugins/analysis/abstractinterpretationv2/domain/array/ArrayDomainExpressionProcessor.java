package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalTermUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ArrayDomainExpressionProcessor<STATE extends IAbstractState<STATE>> {
	private final ArrayDomainToolkit<STATE> mToolkit;
	private final Map<ArrayAccessExpression, IProgramVar> mAuxVarCache;
	private final Map<IProgramVar, ArrayAccessExpression> mAuxVarCacheInverse;

	public ArrayDomainExpressionProcessor(final ArrayDomainToolkit<STATE> toolkit) {
		mToolkit = toolkit;
		mAuxVarCache = new HashMap<>();
		mAuxVarCacheInverse = new HashMap<>();
	}

	public ExpressionResult<STATE> process(final Expression expression, final ArrayDomainState<STATE> state,
			final boolean isAssume) {
		// TODO: For no don't process any expressions (e.g. assume-statements)
		// if (expression instanceof ArrayAccessExpression) {
		// return processArrayAccessExpression((ArrayAccessExpression) expression, state);
		// } else if (expression instanceof BinaryExpression) {
		// return processBinaryExpression((BinaryExpression) expression, state, isAssume);
		// } else if (expression instanceof QuantifierExpression) {
		// return processQuantifierExpression((QuantifierExpression) expression, state, isAssume);
		// } else if (expression instanceof UnaryExpression) {
		// return processUnaryExpression((UnaryExpression) expression, state, isAssume);
		// }
		return new ExpressionResult<>(expression, state);
	}

	private ExpressionResult<STATE> processArrayAccessExpression(final ArrayAccessExpression expression,
			final ArrayDomainState<STATE> state) {
		if (!mAuxVarCache.containsKey(expression)) {
			final IProgramVar created = mToolkit.createValueVar(expression.getType());
			mAuxVarCache.put(expression, created);
			mAuxVarCacheInverse.put(created, expression);
		}
		final IProgramVar auxVar = mAuxVarCache.get(expression);
		final Expression newExpr = getExpression(auxVar);
		ArrayDomainState<STATE> newState = state.addVariable(auxVar);
		final Expression array = expression.getArray();
		final Expression[] indices = expression.getIndices();
		final Script script = mToolkit.getScript();
		// TODO: Multi-dimensional arrays!
		// Add assumptions for the created aux-var based on the segmentation
		if (indices.length == 1) {
			final Expression index = indices[0];
			final Pair<STATE, Segmentation> segmentationPair = newState.getSegmentation(array);
			final Segmentation segmentation = segmentationPair.getSecond();
			final Pair<Integer, Integer> bounds = state.getContainedBoundIndices(segmentation, index);
			final int min = bounds.getFirst();
			final int max = bounds.getSecond();
			final List<Term> disjuncts = new ArrayList<>();
			for (int i = min; i < max; i++) {
				final TermVariable value = segmentation.getValue(i).getTermVariable();
				disjuncts.add(SmtUtils.binaryEquality(script, auxVar.getTermVariable(), value));
			}
			final AssumeStatement assume = createAssume(SmtUtils.or(script, disjuncts));
			final STATE newSubState = mToolkit.handleStatementBySubdomain(segmentationPair.getFirst(), assume);
			newState = newState.updateState(newSubState);
		}
		return new ExpressionResult<>(newExpr, newState);
	}

	private ExpressionResult<STATE> processBinaryExpression(final BinaryExpression expression,
			final ArrayDomainState<STATE> state, final boolean isAssume) {
		final Operator operator = expression.getOperator();
		final Expression left = expression.getLeft();
		final Expression right = expression.getRight();
		switch (operator) {
		case COMPGEQ:
		case COMPGT:
		case COMPLEQ:
		case COMPLT: {
			final ExpressionResult<STATE> leftResult = process(left, state, isAssume);
			final ExpressionResult<STATE> rightResult = process(left, state, isAssume);
			if (isAssume) {
				return processArrayAssumption(leftResult, rightResult, operator);
			}
			return intersectResults(leftResult, rightResult, operator);
		}
		case COMPEQ: {
			if (isBooleanType(left.getType())) {
				final BinaryExpression logicIff =
						new BinaryExpression(null, PrimitiveType.TYPE_BOOL, Operator.LOGICIFF, left, right);
				return processBinaryExpression(logicIff, state, isAssume);
			}
			if (left.getType() instanceof ArrayType) {
				// TODO: a==b
				// final Segmentation leftSegmentation = state.getSegmentation(left);
				// final Segmentation rightSegmentation = state.getSegmentation(right);
			}
			final ExpressionResult<STATE> leftResult = process(left, state, isAssume);
			final ExpressionResult<STATE> rightResult = process(left, state, isAssume);
			if (isAssume) {
				return processArrayAssumption(leftResult, rightResult, operator);
			}
			return intersectResults(leftResult, rightResult, operator);
		}
		case COMPNEQ: {
			if (isBooleanType(left.getType())) {
				final BinaryExpression logicIff =
						new BinaryExpression(null, PrimitiveType.TYPE_BOOL, Operator.LOGICIFF, left, right);
				final UnaryExpression negated =
						new UnaryExpression(null, PrimitiveType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG, logicIff);
				return processUnaryExpression(negated, state, isAssume);
			}
			if (left.getType() instanceof ArrayType) {
				// TODO a!=b (Check if in same equivalence class if identifier expressions)
			}
			return intersectResults(process(left, state, isAssume), process(right, state, isAssume), operator);
		}
		case LOGICIFF:
			final BinaryExpression leftImpl =
					new BinaryExpression(null, PrimitiveType.TYPE_BOOL, Operator.LOGICIMPLIES, left, right);
			final BinaryExpression rightImpl =
					new BinaryExpression(null, PrimitiveType.TYPE_BOOL, Operator.LOGICIMPLIES, right, left);
			final BinaryExpression conjunction =
					new BinaryExpression(null, PrimitiveType.TYPE_BOOL, Operator.LOGICAND, leftImpl, rightImpl);
			return processBinaryExpression(conjunction, state, isAssume);
		case LOGICIMPLIES:
			final Expression leftNegated =
					new UnaryExpression(null, PrimitiveType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG, left);
			final BinaryExpression orExpression =
					new BinaryExpression(null, PrimitiveType.TYPE_BOOL, Operator.LOGICOR, leftNegated, right);
			return processBinaryExpression(orExpression, state, isAssume);
		case LOGICOR:
			return unionResults(process(left, state, isAssume), process(right, state, isAssume), operator);
		default:
			return intersectResults(process(left, state, isAssume), process(right, state, isAssume), operator);
		}
	}

	private ExpressionResult<STATE> processArrayAssumption(final ExpressionResult<STATE> leftResult,
			final ExpressionResult<STATE> rightResult, final Operator operator) {
		// TODO
		return null;
	}

	private ExpressionResult<STATE> processQuantifierExpression(final QuantifierExpression expression,
			final ArrayDomainState<STATE> state, final boolean isAssume) {
		// TODO: Check if has special array form
		return new ExpressionResult<>(expression, state);
	}

	private ExpressionResult<STATE> processUnaryExpression(final UnaryExpression expression,
			final ArrayDomainState<STATE> state, final boolean isAssume) {
		final Expression subExpression = expression.getExpr();
		switch (expression.getOperator()) {
		case ARITHNEGATIVE: {
			final ExpressionResult<STATE> subResult = process(subExpression, state, isAssume);
			final Expression newExpr = new UnaryExpression(null, expression.getOperator(), subResult.getExpression());
			return new ExpressionResult<>(newExpr, subResult.getState());
		}
		case LOGICNEG:
			if (subExpression instanceof UnaryExpression) {
				return process(((UnaryExpression) subExpression).getExpr(), state, isAssume);
			}
			if (subExpression instanceof BinaryExpression) {
				final BinaryExpression binary = negateBinaryExpression((BinaryExpression) subExpression);
				return processBinaryExpression(binary, state, isAssume);
			}
			if (subExpression instanceof QuantifierExpression) {
				final QuantifierExpression quantifier =
						negateQuantifierExpression((QuantifierExpression) subExpression);
				return processQuantifierExpression(quantifier, state, isAssume);
			}
			final ExpressionResult<STATE> subResult = process(subExpression, state, isAssume);
			final Expression newExpr = new UnaryExpression(null, expression.getOperator(), subResult.getExpression());
			return new ExpressionResult<>(newExpr, subResult.getState());
		case OLD:
			// TODO: How to handle this?
		default:
			throw new UnsupportedOperationException("Unsupported operator: " + expression.getOperator());
		}
	}

	private QuantifierExpression negateQuantifierExpression(final QuantifierExpression expression) {
		final Expression newSubformula =
				new UnaryExpression(null, UnaryExpression.Operator.LOGICNEG, expression.getSubformula());
		return new QuantifierExpression(null, expression.isUniversal(), expression.getTypeParams(),
				expression.getParameters(), expression.getAttributes(), newSubformula);
	}

	private BinaryExpression negateBinaryExpression(final BinaryExpression expression) {
		Operator newOp;
		Expression newLeft = expression.getLeft();
		Expression newRight = expression.getRight();
		final ILocation loc = expression.getLocation();
		switch (expression.getOperator()) {
		case COMPEQ:
			newOp = Operator.COMPNEQ;
			break;
		case COMPNEQ:
			newOp = Operator.COMPEQ;
			break;
		case COMPGEQ:
			newOp = Operator.COMPLT;
			break;
		case COMPGT:
			newOp = Operator.COMPLEQ;
			break;
		case COMPLEQ:
			newOp = Operator.COMPGT;
			break;
		case COMPLT:
			newOp = Operator.COMPGEQ;
			break;
		case LOGICAND:
			newOp = Operator.LOGICOR;
			newLeft = new UnaryExpression(loc, BoogieType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG, newLeft);
			newRight = new UnaryExpression(loc, BoogieType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG, newRight);
			break;
		case LOGICOR:
			newOp = Operator.LOGICAND;
			newLeft = new UnaryExpression(loc, BoogieType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG, newLeft);
			newRight = new UnaryExpression(loc, BoogieType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG, newRight);
			break;
		case LOGICIMPLIES:
			newOp = Operator.LOGICAND;
			newRight = new UnaryExpression(loc, BoogieType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG, newRight);
			break;
		case LOGICIFF:
			newOp = Operator.LOGICOR;
			final Expression leftLeft = newLeft;
			final Expression leftRight =
					new UnaryExpression(loc, BoogieType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG, newRight);
			final Expression rightLeft =
					new UnaryExpression(loc, BoogieType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG, newLeft);
			final Expression rightRight = newRight;
			newLeft = new BinaryExpression(loc, BoogieType.TYPE_BOOL, Operator.LOGICAND, leftLeft, leftRight);
			newRight = new BinaryExpression(loc, BoogieType.TYPE_BOOL, Operator.LOGICAND, rightLeft, rightRight);
			break;
		default:
			throw new UnsupportedOperationException("Unsupported operator: " + expression.getOperator());
		}
		return new BinaryExpression(loc, BoogieType.TYPE_BOOL, newOp, newLeft, newRight);
	}

	private Expression getExpression(final IProgramVarOrConst var) {
		return mToolkit.getExpression(getTerm(var));
	}

	private static Term getTerm(final IProgramVarOrConst var) {
		return NonrelationalTermUtils.getTermVar(var);
	}

	private boolean isBooleanType(final IBoogieType type) {
		if (type instanceof PrimitiveType) {
			return (PrimitiveType) type == PrimitiveType.TYPE_BOOL;
		}
		return false;
	}

	private ExpressionResult<STATE> intersectResults(final ExpressionResult<STATE> leftResult,
			final ExpressionResult<STATE> rightResult, final Operator operator) {
		final Expression leftExpression = leftResult.getExpression();
		final Expression rightExpression = rightResult.getExpression();
		final Expression newExpression = new BinaryExpression(null, operator, leftExpression, rightExpression);
		final Set<IProgramVarOrConst> leftAuxVars = rightResult.getState().getUnusedAuxVars();
		final Set<IProgramVarOrConst> rightAuxVars = rightResult.getState().getUnusedAuxVars();
		final ArrayDomainState<STATE> leftState = leftResult.getState().addVariables(rightAuxVars);
		final ArrayDomainState<STATE> rightState = rightResult.getState().addVariables(leftAuxVars);
		final ArrayDomainState<STATE> newState = leftState.intersect(rightState);
		return new ExpressionResult<>(newExpression, newState);
	}

	private ExpressionResult<STATE> unionResults(final ExpressionResult<STATE> leftResult,
			final ExpressionResult<STATE> rightResult, final Operator operator) {
		final Expression leftExpression = leftResult.getExpression();
		final Expression rightExpression = rightResult.getExpression();
		final Expression newExpression = new BinaryExpression(null, operator, leftExpression, rightExpression);
		final Set<IProgramVarOrConst> leftAuxVars = rightResult.getState().getUnusedAuxVars();
		final Set<IProgramVarOrConst> rightAuxVars = rightResult.getState().getUnusedAuxVars();
		final ArrayDomainState<STATE> leftState = leftResult.getState().addVariables(rightAuxVars);
		final ArrayDomainState<STATE> rightState = rightResult.getState().addVariables(leftAuxVars);
		final ArrayDomainState<STATE> newState = leftState.union(rightState);
		return new ExpressionResult<>(newExpression, newState);
	}

	private AssumeStatement createAssume(final Term term) {
		return new AssumeStatement(null, mToolkit.getExpression(term));
	}
}
