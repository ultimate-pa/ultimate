/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.civlizer.model.ParameterDeclaration.Linearity;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;

public class CivlUtils {
	private static final Expression[] EMPTY_EXPRESSIONS = {};

	private CivlUtils() {
		// static utility class should not be instantiated
	}

	static class ExpressionUpdater extends BoogieTransformer {
		static Expression updates(final Expression expr, final CallStatement update) {
			final ExpressionUpdater exprUpdater = new ExpressionUpdater(update);
			return exprUpdater.processExpression(expr);
		}

		private final String mGhostVariable;
		private Expression mCondition = null;

		ExpressionUpdater(final CallStatement update) {
			mGhostVariable = update.getMethodName();
			if (update.getArguments()[0] instanceof final IfThenElseExpression ite) {
				mCondition = processExpression(ite.getCondition());
				final Expression thenPart = processExpression(ite.getThenPart());
				final Expression elsePart = processExpression(ite.getElsePart());
				if (mCondition != ite.getCondition() || thenPart != ite.getThenPart()
						|| elsePart != ite.getElsePart()) {
					final Expression newExpr = new IfThenElseExpression(ite.getLocation(), thenPart.getType(),
							mCondition, thenPart, elsePart);
				}
			}
		}

		@Override
		protected Expression processExpression(final Expression expr) {
			Expression newExpr = null;
			if (expr instanceof final BinaryExpression binexp) {
				final Expression left = processExpression(binexp.getLeft());
				final Expression right = processExpression(binexp.getRight());
				if (left != binexp.getLeft() || right != binexp.getRight()) {
					newExpr = new BinaryExpression(expr.getLocation(), binexp.getType(), binexp.getOperator(), left,
							right);
				}
			} else if (expr instanceof final UnaryExpression unexp) {
				final Expression subexpr = processExpression(unexp.getExpr());
				if (subexpr != unexp.getExpr()) {
					newExpr = new UnaryExpression(expr.getLocation(), unexp.getType(), unexp.getOperator(), subexpr);
				}
			} else if (expr instanceof final ArrayAccessExpression aaexpr) {
				final Expression arr = processExpression(aaexpr.getArray());
				final Expression[] indices = aaexpr.getIndices();
				final Expression[] newIndices = processExpressions(indices);
				if (arr != aaexpr.getArray() || indices != newIndices) {
					newExpr = new ArrayAccessExpression(aaexpr.getLocation(), aaexpr.getType(), arr, newIndices);
				}
			} else if (expr instanceof final ArrayStoreExpression aaexpr) {
				final Expression arr = processExpression(aaexpr.getArray());
				final Expression value = processExpression(aaexpr.getValue());
				final Expression[] indices = aaexpr.getIndices();
				final Expression[] newIndices = processExpressions(indices);
				if (arr != aaexpr.getArray() || indices != newIndices || value != aaexpr.getValue()) {
					newExpr = new ArrayStoreExpression(aaexpr.getLocation(), aaexpr.getType(), arr, newIndices, value);
				}
			} else if (expr instanceof final BitVectorAccessExpression bvaexpr) {
				final Expression bv = processExpression(bvaexpr.getBitvec());
				if (bv != bvaexpr.getBitvec()) {
					newExpr = new BitVectorAccessExpression(bvaexpr.getLocation(), bvaexpr.getType(), bv,
							bvaexpr.getEnd(), bvaexpr.getStart());
				}
			} else if (expr instanceof final FunctionApplication app) {
				final String name = app.getIdentifier();
				final Expression[] args = processExpressions(app.getArguments());
				if (args != app.getArguments()) {
					newExpr = new FunctionApplication(app.getLocation(), app.getType(), name, args);
				}
			} else if (expr instanceof final IfThenElseExpression ite) {
				final Expression cond = processExpression(ite.getCondition());
				final Expression thenPart = processExpression(ite.getThenPart());
				final Expression elsePart = processExpression(ite.getElsePart());
				if (cond != ite.getCondition() || thenPart != ite.getThenPart() || elsePart != ite.getElsePart()) {
					newExpr = new IfThenElseExpression(ite.getLocation(), thenPart.getType(), cond, thenPart, elsePart);
				}
			} else if (expr instanceof final QuantifierExpression quant) {
				final Attribute[] attrs = quant.getAttributes();
				final Attribute[] newAttrs = processAttributes(attrs);
				final VarList[] params = quant.getParameters();
				final VarList[] newParams = processVarLists(params);
				final Expression subform = processExpression(quant.getSubformula());
				if (subform != quant.getSubformula() || attrs != newAttrs || params != newParams) {
					newExpr = new QuantifierExpression(quant.getLocation(), quant.getType(), quant.isUniversal(),
							quant.getTypeParams(), newParams, newAttrs, subform);
				}
			} else if (expr instanceof final StructConstructor sConst) {
				final Expression[] fieldValues = processExpressions(sConst.getFieldValues());
				if (fieldValues != sConst.getFieldValues()) {
					newExpr = new StructConstructor(sConst.getLocation(), sConst.getType(),
							sConst.getFieldIdentifiers(), fieldValues);
				}
			} else if (expr instanceof final StructAccessExpression sae) {
				final Expression struct = processExpression(sae.getStruct());
				if (struct != sae.getStruct()) {
					newExpr = new StructAccessExpression(sae.getLocation(), sae.getType(), struct, sae.getField());
				}
			} else if (expr instanceof BooleanLiteral) {
			} else if (expr instanceof IntegerLiteral) {
			} else if (expr instanceof BitvecLiteral) {
			} else if (expr instanceof StringLiteral) {
			} else if (expr instanceof IdentifierExpression) {
			} else if (expr instanceof WildcardExpression) {
			} else if (expr instanceof RealLiteral) {
			} else if (expr == null) {
				throw new IllegalArgumentException("expression may not be null");
			} else {
				throw new UnsupportedOperationException("unknown expression " + expr.getClass().getName());
			}

			if (newExpr == null || newExpr == expr) {
				/*
				 * BooleanLiteral, IntegerLiteral, BitvecLiteral, StringLiteral, IdentifierExpression and
				 * WildcardExpression do not need recursion, and recursion can leave the expression unchanged.
				 */
				return expr;
			}
			ModelUtils.copyAnnotations(expr, newExpr);
			return newExpr;
		}

	}

	static Expression updateAnnotation(final Expression annotation, final List<CallStatement> ghostUpdates) {
		// TODO finish
		for (final var ghostUpdate : ghostUpdates) {

		}

		return annotation;
	}

	static Attribute createLinearityAttribute(final Linearity linearity) {
		final String name = switch (linearity) {
		case IN -> "linear_in";
		case OUT -> "linear_out";
		case INOUT -> "linear";
		case NONE -> throw new IllegalArgumentException();
		};
		return new NamedAttribute(null, name, EMPTY_EXPRESSIONS);
	}

	static NamedAttribute createLayerAttribute(final int introductionLayer, final int disappearingLayer) {
		final var introductionLit = new IntegerLiteral(null, BoogieType.TYPE_INT, String.valueOf(introductionLayer));
		final var disappearingLit = new IntegerLiteral(null, BoogieType.TYPE_INT, String.valueOf(disappearingLayer));
		return new NamedAttribute(null, "layer", new Expression[] { introductionLit, disappearingLit });
	}

	static NamedAttribute createLayerAttribute(final int layer) {
		final var lit = new IntegerLiteral(null, BoogieType.TYPE_INT, String.valueOf(layer));
		return new NamedAttribute(null, "layer", new Expression[] { lit });
	}

	static NamedAttribute createYieldsAttribute() {
		return new NamedAttribute(null, "yields", EMPTY_EXPRESSIONS);
	}

	static Expression createYieldCallExpression(final CallStatement call) {
		assert call.getLhs() == null || call.getLhs().length == 0 : "Call with outputs is not a yield call expression";
		assert !call.isForall() : "Forall call is not a yield call expression";
		final var funApp = new FunctionApplication(call.getLoc(), call.getMethodName(), call.getArguments());
		new CivlYieldCallAnnotation().annotate(funApp);
		return funApp;
	}

	static CallStatement recreateYieldCall(final FunctionApplication funApp) {
		assert CivlYieldCallAnnotation.isYieldCall(funApp) : "Expression was not marked as a yield call.";
		return new CallStatement(funApp.getLoc(), false, new VariableLHS[0], funApp.getIdentifier(),
				funApp.getArguments());
	}
}
