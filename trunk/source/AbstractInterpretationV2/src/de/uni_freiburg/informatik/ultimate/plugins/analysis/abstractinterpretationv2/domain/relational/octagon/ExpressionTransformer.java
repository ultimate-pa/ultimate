package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtil;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

public class ExpressionTransformer {

	private Map<Expression, AffineExpression> mCacheAffineExpr = new HashMap<>();
	private Map<Expression, Expression> mCacheLogicNeg = new HashMap<>();
	private Map<Expression, List<Pair<List<Expression>, Expression>>> mCacheRemoveIfExpr = new HashMap<>();
	
	public AffineExpression affineExprCached(Expression e) {
		AffineExpression cachedAe = mCacheAffineExpr.get(e);
		if (cachedAe == null) {
			cachedAe = toAffineExpr(e);
			if (cachedAe != null) {
				mCacheAffineExpr.put(e, cachedAe);
			}
		}
		return cachedAe;
	}

	// TODO implement transformation to AffineExpression, using known concrete values
	// (x = [1, 1] is concrete, y = [1, 2] is not.)

	public Expression logicNegCached(Expression e) {
		Expression cachedLn = mCacheLogicNeg.get(e);
		if (cachedLn == null) {
			cachedLn = encloseInLogicNeg(e);
			if (cachedLn != null) {
				mCacheLogicNeg.put(e, cachedLn);
			}
		}
		return cachedLn;
	}

	public List<Pair<List<Expression>, Expression>> removeIfExprsCached(Expression e) {
		List<Pair<List<Expression>, Expression>> cachedPaths = mCacheRemoveIfExpr.get(e);
		if (cachedPaths == null) {
			cachedPaths = removeIfExprs(e);
			if (cachedPaths != null) {
				mCacheRemoveIfExpr.put(e, cachedPaths);
			}
		}
		return cachedPaths;
	}
	
	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	
	private AffineExpression toAffineExpr(Expression e) {
		assert TypeUtil.isNumeric(e.getType()) : "Cannot transform non-numeric expression to affine expression: " + e;
		if (e instanceof IntegerLiteral) {
			String value = ((IntegerLiteral) e).getValue();
			return new AffineExpression(new BigDecimal(value));
		} else if (e instanceof RealLiteral) {
			String value = ((RealLiteral) e).getValue();
			return new AffineExpression(new BigDecimal(value));
		} else if (e instanceof IdentifierExpression) {
			String varName = ((IdentifierExpression) e).getIdentifier();
			Map<String, BigDecimal> coefficients = Collections.singletonMap(varName, BigDecimal.ONE);
			return new AffineExpression(coefficients, BigDecimal.ZERO);
		} else if (e instanceof UnaryExpression) {
			return unaryExprToAffineExpr((UnaryExpression) e);
		} else if (e instanceof BinaryExpression) {
			return binaryExprToAffineExpr((BinaryExpression) e);
		}
		return null;
	}

	private AffineExpression unaryExprToAffineExpr(UnaryExpression e) {
		switch (e.getOperator()) {
		case ARITHNEGATIVE:
			AffineExpression sub = toAffineExpr(e.getExpr());
			return sub == null ? null : sub.negate();
		default:
			return null;
		}
	}
	
	private AffineExpression binaryExprToAffineExpr(BinaryExpression e) {
		AffineExpression left = toAffineExpr(e.getLeft());
		if (left == null) { return null; }
		AffineExpression right = toAffineExpr(e.getRight());
		if (right == null) { return null; }
		boolean isInteger = TypeUtil.isNumericInt(e.getType());
		switch (e.getOperator()) {
		case ARITHDIV:
			return left.divide(right, isInteger);
		case ARITHMINUS:
			return left.add(right.negate());
		case ARITHMOD:
			return left.modulo(right);
		case ARITHMUL:
			return left.multiply(right);
		case ARITHPLUS:
			return left.add(right);
		default:
			return null;
		}
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	private Expression encloseInLogicNeg(Expression e) {
		assert TypeUtil.isBoolean(e.getType()) : "Logical negation of non-boolean expression: " + e;
		return new UnaryExpression(e.getLocation(), e.getType(), UnaryExpression.Operator.LOGICNEG, e);
	}

	/*
	private Expression toLogicNegation(Expression e) {
		assert TypeUtil.isBoolean(e.getType()) : "Logical negation of non-boolean expression: " + e;
		if (e instanceof BinaryExpression) {
			return binaryExpressionToLogicNegation((BinaryExpression) e);
		}
		return null; // TODO
	}

	private Expression binaryExpressionToLogicNegation(BinaryExpression e) {
		BinaryExpression.Operator negOp = null;
		boolean negateSubExpr = false;
		switch (e.getOperator()) {
		case COMPEQ:
			negOp = Operator.COMPNEQ;
			break;
		case COMPNEQ:
			negOp = Operator.COMPEQ;
			break;
		case COMPGEQ:
			negOp = Operator.COMPLT;
			break;
		case COMPLT:
			negOp = Operator.COMPGEQ;
			break;
		case COMPGT:
			negOp = Operator.COMPLEQ;
			break;
		case COMPLEQ:
			negOp = Operator.COMPGT;
			break;
		case LOGICAND:
			negOp = Operator.LOGICOR;
			negateSubExpr = true;
			break;
		case LOGICOR:
			negOp = Operator.LOGICAND;
			negateSubExpr = true;
			break;
		case LOGICIFF:
			// TODO
			throw new UnsupportedOperationException("Negation of '<=>' not yet implemented.");
			// break;
		case LOGICIMPLIES:
			// TODO
			throw new UnsupportedOperationException("Negation of '=>' not yet implemented.");
			// break;s
		case COMPPO: // partial order "<:"
			return encloseInLogicNeg(e);
		case BITVECCONCAT:
			throw new IllegalArgumentException("Logical negation of bit-vector concat: " + e);
		case ARITHDIV:
		case ARITHMINUS:
		case ARITHMOD:
		case ARITHMUL:
		case ARITHPLUS:
			throw new IllegalArgumentException("Logical negation of arithmetic operator: " + e);
		default:
			throw new UnsupportedOperationException("Unknown binary operator: " + e);
		}
		throw new UnsupportedOperationException("logical negation not yet implemented.");
		// return null; // TODO
	}
	*/

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	private List<Pair<List<Expression>, Expression>> removeIfExprs(Expression e) {
		if (e instanceof IfThenElseExpression) {
			return removeIfExprsFromIfExpr((IfThenElseExpression) e);
		} else if (e instanceof BinaryExpression) {
			return removeIfExprsFromBinaryExpr((BinaryExpression) e);
		} else if (e instanceof UnaryExpression) {
			return removeIfExprsFromUnaryExpr((UnaryExpression) e);
		} else {
			// Expression does not contain further expressions
			// except for Quantifiers or Array*Expressions -- but they are are not interpreted by the post-operator
			return pathWithoutIfs(e);
		}
	}

	private List<Pair<List<Expression>, Expression>> removeIfExprsFromIfExpr(IfThenElseExpression e) {
		List<Pair<List<Expression>, Expression>> thenPaths, elsePaths;
		thenPaths = removeIfExprs(e.getThenPart());
		elsePaths = removeIfExprs(e.getElsePart());
		Expression condition, notCondition;
		condition = e.getCondition();
		// note: condition may contain further IfThenElseExpressions which will not be removed.
		if (!(condition instanceof WildcardExpression)) {
			notCondition = logicNegCached(condition);
			thenPaths.forEach(p -> p.getFirst().add(condition));
			elsePaths.forEach(p -> p.getFirst().add(notCondition));
			// note: Assumptions are added to the end of the list. Results in "innermost if-condition first".
			//       Not wrong, but interpretation MAY be not as precise (depending on abstr. domain and post-operator).
		}
		return concatLists(thenPaths, elsePaths);
	}
	
	private List<Pair<List<Expression>, Expression>> removeIfExprsFromBinaryExpr(BinaryExpression e) {
		List<Pair<List<Expression>, Expression>> leftPaths, rightPaths;
		leftPaths = removeIfExprs(e.getLeft());
		rightPaths = removeIfExprs(e.getRight());
		if (leftPaths.size() == 1 && rightPaths.size() == 1) {
			// TODO remove assertion (complete line)
			assert leftPaths.get(0).getSecond() == e.getLeft() && rightPaths.get(0).getSecond() == e.getRight()
					&& leftPaths.get(0).getFirst().isEmpty() && rightPaths.get(0).getFirst().isEmpty();
			return pathWithoutIfs(e);
		} else {
			int cartesianProductSize = leftPaths.size() * rightPaths.size();
			List<Pair<List<Expression>, Expression>> newPaths = new ArrayList<>(cartesianProductSize);
			for (Pair<List<Expression>, Expression> pl : leftPaths) {
				for (Pair<List<Expression>, Expression> pr : rightPaths) {
					newPaths.add(new Pair<>(concatLists(pl.getFirst(), pr.getFirst()), new BinaryExpression(
							e.getLocation(), e.getType(), e.getOperator(), pl.getSecond(), pr.getSecond())));
				}
			}
			return newPaths;
		}
	}
	
	private List<Pair<List<Expression>, Expression>> removeIfExprsFromUnaryExpr(UnaryExpression e) {
		List<Pair<List<Expression>, Expression>> paths = removeIfExprs(e.getExpr());
		if (paths.size() == 1) {
			// TODO remove assertion (complete line)
			assert paths.get(0).getSecond() == e.getExpr() && paths.get(0).getFirst().isEmpty();
			return pathWithoutIfs(e);
		} else {
			// modify paths in-place (value is used only here)
			for (int i = 0; i < paths.size(); ++i) {
				Pair<List<Expression>, Expression> p = paths.get(i);
				paths.set(i, new Pair<>(p.getFirst(),
						new UnaryExpression(e.getLocation(), e.getType(), e.getOperator(), p.getSecond())));
			}
			return paths;
		}
	}
	
	private List<Pair<List<Expression>, Expression>> pathWithoutIfs(Expression e) {
		// "new ArrayList()" instead of "Collection.emptyList()" allows to add values later on (and is NOT slower!)
		return Collections.singletonList(new Pair<>(new ArrayList<>(), e));
	}
	
	private <T> List<T> concatLists(List<T> first, List<T> second) {
		List<T> result = new ArrayList<>(first.size() + second.size());
		result.addAll(first);
		result.addAll(second);
		return result;
	}

}








