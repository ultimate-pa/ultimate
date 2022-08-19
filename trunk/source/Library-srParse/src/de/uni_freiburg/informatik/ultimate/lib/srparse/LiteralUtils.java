/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.srparse;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class LiteralUtils {

	private LiteralUtils() {
		// do not construct utility class
	}

	/**
	 * Convert literal expression to {@link Term}.
	 */
	public static Optional<Term> toTerm(final Expression expr, final Script script) {
		if (expr instanceof RealLiteral) {
			return Optional
					.of(SmtUtils.toRational(((RealLiteral) expr).getValue()).toTerm(SmtSortUtils.getRealSort(script)));
		} else if (expr instanceof IntegerLiteral) {
			return Optional.of(
					SmtUtils.toRational(((IntegerLiteral) expr).getValue()).toTerm(SmtSortUtils.getIntSort(script)));
		} else if (expr instanceof BooleanLiteral) {
			if (((BooleanLiteral) expr).getValue()) {
				return Optional.of(script.term("true"));
			}
			return Optional.of(script.term("false"));
		} else if (expr instanceof UnaryExpression) {
			final UnaryExpression uexpr = (UnaryExpression) expr;
			if (uexpr.getOperator() == Operator.ARITHNEGATIVE) {
				return toTerm(uexpr.getExpr(), script).map(a -> SmtUtils.neg(script, a));
			}
		}
		return Optional.empty();
	}

	/**
	 * Convert numeric literal expression to {@link Rational}
	 */
	public static Optional<Rational> toRational(final Expression expr) {
		if (expr instanceof UnaryExpression) {
			final UnaryExpression uexpr = (UnaryExpression) expr;
			if (uexpr
					.getOperator() == de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator.ARITHNEGATIVE) {
				return toRational(uexpr.getExpr()).map(a -> a.negate());
			}
		} else if (expr instanceof RealLiteral) {
			return Optional.of(SmtUtils.toRational(((RealLiteral) expr).getValue()));
		} else if (expr instanceof IntegerLiteral) {
			return Optional.of(SmtUtils.toRational(((IntegerLiteral) expr).getValue()));
		}
		return Optional.empty();
	}

	public static Expression toExpression(final ILocation loc, final Rational r, final boolean beReal) {
		if (!r.isRational()) {
			final Expression left = new IntegerLiteral(loc, BoogieType.TYPE_INT, r.numerator().toString());
			final Expression right = new IntegerLiteral(loc, BoogieType.TYPE_INT, r.denominator().toString());
			return new BinaryExpression(loc, BoogieType.TYPE_REAL,
					de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator.ARITHDIV, left, right);

		}
		if (r.isIntegral() && r.denominator().equals(BigInteger.ONE)) {
			if (beReal) {
				return new RealLiteral(loc, BoogieType.TYPE_REAL, r.numerator().toString());
			}
			return new IntegerLiteral(loc, BoogieType.TYPE_INT, r.numerator().toString());
		}
		final String stringVal = new BigDecimal(r.numerator()).divide(new BigDecimal(r.denominator())).toPlainString();
		return new RealLiteral(loc, BoogieType.TYPE_REAL, stringVal);
	}

}
