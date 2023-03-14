/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;

/**
 * Methods to transform Boogie expressions into {@link AffineExpression}s {@link IfThenElseExpression}-free expressions
 * and logic negations. Transformations are cached.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class ExpressionTransformer {

	/**
	 * Cache of already processed expressions and their affine version. Expressions that are not present as a map key
	 * were never processed. Expressions that map to {@code null} were processed, but could not be transformed.
	 */
	private final Map<Expression, AffineExpression> mCacheAffineExpr;

	/**
	 * Cache of already processed expressions and their logical negation. Expressions that are not present as a map key
	 * were never processed.
	 */
	private final Map<Expression, Expression> mCacheLogicNeg;

	/**
	 * Cache of already processed expressions and their if-free version. Expressions that are not present as a map key
	 * were never processed.
	 */
	private final Map<Expression, IfExpressionTree> mCacheRemoveIfExpr;

	private final IBoogieSymbolTableVariableProvider mBpl2SmtSymbolTable;

	ExpressionTransformer(final IBoogieSymbolTableVariableProvider bpl2smtSymbolTable) {
		mCacheRemoveIfExpr = new HashMap<>();
		mCacheLogicNeg = new HashMap<>();
		mCacheAffineExpr = new HashMap<>();
		mBpl2SmtSymbolTable = bpl2smtSymbolTable;
	}

	/**
	 * Transform an expression into an {@link AffineExpression}. Expressions that cannot be transformed result in
	 * {@code null}.
	 * <p>
	 * The result of the transformation is cached -- subsequent calls with the same parameter will return the very same
	 * object.
	 *
	 * @param expr
	 *            Expression to be transformed.
	 * @return {@link AffineExpression} or {@code null}
	 */
	public AffineExpression affineExprCached(final Expression expr) {
		if (mCacheAffineExpr.containsKey(expr)) {
			return mCacheAffineExpr.get(expr); // may return null
		}
		final AffineExpression cachedAffExpr = toAffineExpr(expr);
		mCacheAffineExpr.put(expr, cachedAffExpr);
		return cachedAffExpr;
	}

	// TODO implement transformation to AffineExpression, using known concrete values
	// (x = [1, 1] is concrete, y = [1, 2] is not.)

	/**
	 * Negate a boolean expression. The negation is not deep. The resulting negation of {@code x < y} is
	 * {@code !(x < y)} and not {@code x >= y}. Only boolean literals and already negated expressions (for instance
	 * {@code !(expr)} are negated without enclosing them in a further negation.
	 * <p>
	 * The result of the transformation is cached -- subsequent calls with the same parameter will return the very same
	 * object.
	 *
	 * @param expr
	 *            Expression to be transformed.
	 * @return Logical negation
	 */
	public Expression logicNegCached(final Expression expr) {
		Expression cachedNeg = mCacheLogicNeg.get(expr);
		if (cachedNeg == null) {
			cachedNeg = logicNeg(expr);
			mCacheLogicNeg.put(expr, cachedNeg);
		}
		return cachedNeg;
	}

	/**
	 * Removes {@link IfThenElseExpression}s from an expression. Each {@code if} is substituted by two assume
	 * statements. {@code if}s inside the body of other {@code if}s are removed. {@code if}s inside the conditions of
	 * other {@code if}s are <b>not</b> removed.
	 * <p>
	 * The result of the transformation is cached -- subsequent calls with the same parameter will return the very same
	 * object.
	 *
	 * @param expr
	 *            Expression to be transformed.
	 * @return Expression without {@code if}s
	 *
	 * @see IfExpressionTree
	 */
	public IfExpressionTree removeIfExprsCached(final Expression expr) {
		IfExpressionTree cachedTree = mCacheRemoveIfExpr.get(expr);
		if (cachedTree == null) {
			// cachedTree = removeIfExprs(e);
			cachedTree = IfExpressionTree.buildTree(expr, this);
			mCacheRemoveIfExpr.put(expr, cachedTree);
		}
		return cachedTree;
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	/** Internal, non-cached version of {@link #affineExprCached(Expression)}. */
	private AffineExpression toAffineExpr(final Expression expr) {
		assert TypeUtils.isNumeric(expr.getType()) : "Cannot transform non-numeric expression to affine expression: "
				+ expr;
		if (expr instanceof IntegerLiteral) {
			final String value = ((IntegerLiteral) expr).getValue();
			return new AffineExpression(AbsIntUtil.sanitizeBigDecimalValue(value));
		} else if (expr instanceof RealLiteral) {
			final String value = ((RealLiteral) expr).getValue();
			return new AffineExpression(AbsIntUtil.sanitizeBigDecimalValue(value));
		} else if (expr instanceof IdentifierExpression) {
			final IdentifierExpression ie = (IdentifierExpression) expr;
			IProgramVarOrConst var =
					mBpl2SmtSymbolTable.getBoogieVar(ie.getIdentifier(), ie.getDeclarationInformation(), false);
			if (var == null) {
				var = mBpl2SmtSymbolTable.getBoogieConst(ie.getIdentifier());
			}
			assert var != null;
			final Map<IProgramVarOrConst, BigDecimal> coefficients = Collections.singletonMap(var, BigDecimal.ONE);
			return new AffineExpression(coefficients, BigDecimal.ZERO);
		} else if (expr instanceof UnaryExpression) {
			final UnaryExpression uexpr = (UnaryExpression) expr;
			if (uexpr.getOperator() == Operator.OLD) {
				if (!(uexpr.getExpr() instanceof IdentifierExpression)) {
					throw new UnsupportedOperationException("No support for old expressions yet");
				}
				final IdentifierExpression oldIe = (IdentifierExpression) uexpr.getExpr();
				IProgramVarOrConst var = mBpl2SmtSymbolTable.getBoogieVar(oldIe.getIdentifier(),
						oldIe.getDeclarationInformation(), true);
				if (var == null) {
					var = mBpl2SmtSymbolTable.getBoogieConst(oldIe.getIdentifier());
				}
				assert var != null;
				final Map<IProgramVarOrConst, BigDecimal> coefficients = Collections.singletonMap(var, BigDecimal.ONE);
				return new AffineExpression(coefficients, BigDecimal.ZERO);
			}
			return unaryExprToAffineExpr(uexpr);
		} else if (expr instanceof BinaryExpression) {
			return binaryExprToAffineExpr((BinaryExpression) expr);
		}
		return null;
	}

	/** @see #toAffineExpr(Expression) */
	private AffineExpression unaryExprToAffineExpr(final UnaryExpression expr) {
		switch (expr.getOperator()) {
		case ARITHNEGATIVE:
			final AffineExpression sub = affineExprCached(expr.getExpr());
			return sub == null ? null : sub.negate();
		case OLD:
			return affineExprCached(expr);
		default:
			return null;
		}
	}

	/** @see #toAffineExpr(Expression) */
	private AffineExpression binaryExprToAffineExpr(final BinaryExpression expr) {
		final AffineExpression left = affineExprCached(expr.getLeft());
		if (left == null) {
			return null;
		}
		final AffineExpression right = affineExprCached(expr.getRight());
		if (right == null) {
			return null;
		}
		final boolean isInteger = TypeUtils.isNumericInt(expr.getType());
		switch (expr.getOperator()) {
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

	/** Internal, non-cached version of {@link #logicNeg(Expression)}. */
	private static Expression logicNeg(final Expression expr) {
		assert TypeUtils.isBoolean(expr.getType()) : "Logical negation of non-boolean expression: " + expr;
		if (expr instanceof UnaryExpression) {
			final UnaryExpression unaryExpr = (UnaryExpression) expr;
			if (unaryExpr.getOperator() == UnaryExpression.Operator.LOGICNEG) {
				return unaryExpr.getExpr();
			}
		} else if (expr instanceof BooleanLiteral) {
			final BooleanLiteral boolLit = (BooleanLiteral) expr;
			return new BooleanLiteral(boolLit.getLocation(), boolLit.getType(), !boolLit.getValue());
		}
		return new UnaryExpression(expr.getLocation(), expr.getType(), UnaryExpression.Operator.LOGICNEG, expr);
	}

}
