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

	public Expression toBoogie(final CDD cdd, final BoogieLocation bl) {
		if (cdd == CDD.TRUE) {
			return new BooleanLiteral(bl, true);
		}
		if (cdd == CDD.FALSE) {
			return new BooleanLiteral(bl, false);
		}
		final CDD simplifiedCdd = cdd.getDecision().simplify(cdd.getChilds());
		if (simplifiedCdd == CDD.TRUE) {
			return new BooleanLiteral(bl, true);
		}
		if (simplifiedCdd == CDD.FALSE) {
			return new BooleanLiteral(bl, false);
		}
		final CDD[] childs = simplifiedCdd.getChilds();
		final Decision<?> decision = simplifiedCdd.getDecision();

		Expression rtr = null;
		for (int i = 0; i < childs.length; i++) {
			if (childs[i] == CDD.FALSE) {
				continue;
			}
			Expression childExpr = toBoogie(childs[i], bl);
			if (!simplifiedCdd.childDominates(i)) {
				Expression decisionExpr;

				if (decision instanceof RangeDecision) {
					// TODO: I added negation by restructuring, is this wrong?
					decisionExpr =
							toExpressionForRange(i, decision.getVar(), ((RangeDecision) decision).getLimits(), bl);
				} else if (decision instanceof BoogieBooleanExpressionDecision) {
					decisionExpr = ((BoogieBooleanExpressionDecision) decision).getExpression();
				} else if (decision instanceof BooleanDecision) {
					// TODO: This also covers RelationDecisions, is this intended?
					decisionExpr = new IdentifierExpression(bl, ((BooleanDecision) decision).getVar());
				} else if (decision instanceof EventDecision) {
					decisionExpr = new IdentifierExpression(bl, ((EventDecision) decision).getVar());
				} else {
					throw new UnsupportedOperationException("Unknown decision type: " + decision.getClass());
				}

				if (i == 1 && !(decision instanceof RangeDecision)) {
					// negate if right child
					decisionExpr = new UnaryExpression(bl, UnaryExpression.Operator.LOGICNEG, decisionExpr);
				}

				if (childExpr instanceof BooleanLiteral && ((BooleanLiteral) childExpr).getValue()) {
					childExpr = decisionExpr;
				} else {
					childExpr = new BinaryExpression(bl, BinaryExpression.Operator.LOGICAND, decisionExpr, childExpr);
				}
			}
			if (rtr == null) {
				rtr = childExpr;
			} else {
				rtr = new BinaryExpression(bl, BinaryExpression.Operator.LOGICOR, childExpr, rtr);
			}
		}

		if (rtr == null) {
			return new BooleanLiteral(bl, false);
		}
		return rtr;
	}

	public static Expression toExpressionForRange(final int childIdx, final String var, final int[] limits,
			final BoogieLocation bl) {
		if (childIdx == 0) {
			// only upper bound
			final IdentifierExpression lhs = new IdentifierExpression(bl, var);
			final RealLiteral rhs = new RealLiteral(bl, Double.toString(limits[0] / 2));
			if ((limits[0] & 1) == 0) {
				// strict because of first bit encoding
				return new BinaryExpression(bl, BinaryExpression.Operator.COMPLT, lhs, rhs);
			}
			// not strict
			return new BinaryExpression(bl, BinaryExpression.Operator.COMPLEQ, lhs, rhs);
		}

		if (childIdx == limits.length) {
			// only lower bound
			final IdentifierExpression lhs = new IdentifierExpression(bl, var);
			final RealLiteral rhs = new RealLiteral(bl, Double.toString(limits[limits.length - 1] / 2));
			if ((limits[limits.length - 1] & 1) == 1) {
				return new BinaryExpression(bl, BinaryExpression.Operator.COMPGT, lhs, rhs);
			}
			return new BinaryExpression(bl, BinaryExpression.Operator.COMPGEQ, lhs, rhs);
		}

		if ((limits[childIdx - 1] / 2) == (limits[childIdx] / 2)) {
			// we have upper and lower, but they are identical, so its EQ
			// and they differ in the first bit because first bit encoding and sortedness
			final IdentifierExpression rhs = new IdentifierExpression(bl, var);
			final RealLiteral lhs = new RealLiteral(bl, Double.toString(limits[childIdx] / 2));
			return new BinaryExpression(bl, BinaryExpression.Operator.COMPEQ, rhs, lhs);
		}

		// we have upper and lower bounds
		final RealLiteral lb = new RealLiteral(bl, Double.toString(limits[childIdx - 1] / 2));
		final RealLiteral ub = new RealLiteral(bl, Double.toString(limits[childIdx] / 2));
		final IdentifierExpression idExpr = new IdentifierExpression(bl, var);
		final BinaryExpression lbExpr;
		final BinaryExpression ubExpr;
		if ((limits[childIdx - 1] & 1) == 1) {
			// strict lb
			lbExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPLT, lb, idExpr);
		} else {
			lbExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPLEQ, lb, idExpr);
		}

		if ((limits[childIdx] & 1) == 0) {
			// strict ub
			ubExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPLT, idExpr, ub);
		} else {
			ubExpr = new BinaryExpression(bl, BinaryExpression.Operator.COMPLEQ, idExpr, ub);
		}

		return new BinaryExpression(bl, BinaryExpression.Operator.LOGICAND, lbExpr, ubExpr);
	}
}
