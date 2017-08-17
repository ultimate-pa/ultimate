/*
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.lib.pea.BoogieBooleanExpressionDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;

public class CDDTranslator {

	public Expression CDD_To_Boogie(CDD cdd, final String fileName, final BoogieLocation bl) {
		final Expression falseExpr = new BooleanLiteral(bl, false);
		Expression expr = falseExpr;

		if (cdd == CDD.TRUE) {
			final BooleanLiteral bLiteral = new BooleanLiteral(bl, true);
			return bLiteral;
		}
		if (cdd == CDD.FALSE) {
			return falseExpr;
		}
		CDD[] childs = cdd.getChilds();
		Decision decision = cdd.getDecision();
		cdd = decision.simplify(childs);
		if (cdd == CDD.TRUE) {
			return new BooleanLiteral(bl, true);
		}
		if (cdd == CDD.FALSE) {
			return new BooleanLiteral(bl, false);
		}
		childs = cdd.getChilds();
		decision = cdd.getDecision();

		for (int i = 0; i < childs.length; i++) {

			if (childs[i] == CDD.FALSE) {
				continue;
			}
			Expression childExpr = CDD_To_Boogie(childs[i], fileName, bl);
			if (!cdd.childDominates(i)) {
				Expression decisionExpr;

				if (decision instanceof RangeDecision) {
					decisionExpr = toExpressionForRange(i, decision.getVar(), ((RangeDecision) decision).getLimits(),
							fileName, bl);
				} else if (decision instanceof BoogieBooleanExpressionDecision) {
					decisionExpr = ((BoogieBooleanExpressionDecision) decision).getExpression();
					if (i == 1) {
						decisionExpr = new UnaryExpression(decisionExpr.getLocation(),
								UnaryExpression.Operator.LOGICNEG, decisionExpr);
					}
				} else {
					String varName;
					if (decision instanceof BooleanDecision) {
						varName = ((BooleanDecision) decision).getVar();
					} else {
						varName = ((EventDecision) decision).getEvent();
					}
					decisionExpr = new IdentifierExpression(bl, varName);
					decisionExpr = new UnaryExpression(bl, UnaryExpression.Operator.LOGICNEG, decisionExpr);
				}

				if (childExpr instanceof BooleanLiteral && ((BooleanLiteral) childExpr).getValue()) {
					childExpr = decisionExpr;
				} else {
					childExpr = new BinaryExpression(bl, BinaryExpression.Operator.LOGICAND, decisionExpr, childExpr);
				}
			}
			if (expr == falseExpr) {
				expr = childExpr;
			} else {
				expr = new BinaryExpression(bl, BinaryExpression.Operator.LOGICOR, childExpr, expr);
			}
		}
		return expr;
	}

	public static Expression toExpressionForRange(final int childs, final String var, final int[] limits,
			final String fileName, final BoogieLocation bl) {
		if (childs == 0) {
			final IdentifierExpression LHS = new IdentifierExpression(bl, var);
			final RealLiteral RHS = new RealLiteral(bl, Double.toString(limits[0] / 2));
			if ((limits[0] & 1) == 0) {
				return new BinaryExpression(bl, BinaryExpression.Operator.COMPLT, LHS, RHS);
			}
			return new BinaryExpression(bl, BinaryExpression.Operator.COMPLEQ, LHS, RHS);
		}

		if (childs == limits.length) {
			final IdentifierExpression LHS = new IdentifierExpression(bl, var);
			final RealLiteral RHS = new RealLiteral(bl, Double.toString(limits[limits.length - 1] / 2));
			if ((limits[limits.length - 1] & 1) == 1) {
				return new BinaryExpression(bl, BinaryExpression.Operator.COMPGT, LHS, RHS);
			}
			return new BinaryExpression(bl, BinaryExpression.Operator.COMPGEQ, LHS, RHS);
		}

		if ((limits[childs - 1] / 2) == (limits[childs] / 2)) {
			final IdentifierExpression LHS = new IdentifierExpression(bl, var);
			final RealLiteral RHS = new RealLiteral(bl, Double.toString(limits[childs] / 2));
			return new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ, LHS, RHS);
		}
		final RealLiteral LHS = new RealLiteral(bl, Double.toString(limits[childs - 1] / 2));
		final RealLiteral RHS = new RealLiteral(bl, Double.toString(limits[childs] / 2));
		final IdentifierExpression varID = new IdentifierExpression(bl, var);
		BinaryExpression expr = null;
		if ((limits[childs - 1] & 1) == 1 & (limits[childs] & 1) == 0) {

			final BinaryExpression RHS_LT_LT = new BinaryExpression(bl, BinaryExpression.Operator.COMPLT, varID, RHS);
			expr = new BinaryExpression(bl, BinaryExpression.Operator.COMPLT, LHS, RHS_LT_LT);

		} else if ((limits[childs - 1] & 1) == 1 & ((limits[childs] & 1) != 0)) {

			final BinaryExpression RHS_LT_LTEQ =
					new BinaryExpression(bl, BinaryExpression.Operator.COMPLEQ, varID, RHS);
			expr = new BinaryExpression(bl, BinaryExpression.Operator.COMPLT, LHS, RHS_LT_LTEQ);

		} else if (((limits[childs - 1] & 1) != 1) & ((limits[childs] & 1) == 0)) {

			final BinaryExpression RHS_LTEQ_LT = new BinaryExpression(bl, BinaryExpression.Operator.COMPLT, varID, RHS);
			expr = new BinaryExpression(bl, BinaryExpression.Operator.COMPLEQ, LHS, RHS_LTEQ_LT);
		} else if (((limits[childs - 1] & 1) != 1) & ((limits[childs] & 1) != 0)) {

			final BinaryExpression RHS_LTEQ_LTEQ =
					new BinaryExpression(bl, BinaryExpression.Operator.COMPLEQ, varID, RHS);
			expr = new BinaryExpression(bl, BinaryExpression.Operator.COMPLEQ, LHS, RHS_LTEQ_LTEQ);
		}
		return expr;
	}
}
