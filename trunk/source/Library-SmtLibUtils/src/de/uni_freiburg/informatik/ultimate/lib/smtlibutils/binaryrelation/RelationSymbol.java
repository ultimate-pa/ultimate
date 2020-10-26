/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE SmtLibUtils Library.
 *
 * The ULTIMATE SmtLibUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SmtLibUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SmtLibUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SmtLibUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SmtLibUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Values of this enum represent the relation symbol of some binary relations.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public enum RelationSymbol {
	EQ("="), DISTINCT("distinct"), LEQ("<="), GEQ(">="), LESS("<"), GREATER(">"), BVULE("bvule"), BVULT("bvult"), BVUGE(
			"bvuge"), BVUGT("bvugt"), BVSLE("bvsle"), BVSLT("bvslt"), BVSGE("bvsge"), BVSGT("bvsgt");

	private final String mStringRepresentation;

	RelationSymbol(final String stringRepresentation) {
		mStringRepresentation = stringRepresentation;
	}

	@Override
	public String toString() {
		return mStringRepresentation;
	}

	/**
	 * @return {@link RelationSymbol} whose string representation is relAsString and null if no {@link RelationSymbol}
	 *         has such a string representation.
	 */
	public static RelationSymbol convert(final String relAsString) {
		switch (relAsString) {
		case "=":
			return RelationSymbol.EQ;
		case "distinct":
			return RelationSymbol.DISTINCT;
		case "<=":
			return RelationSymbol.LEQ;
		case ">=":
			return RelationSymbol.GEQ;
		case "<":
			return RelationSymbol.LESS;
		case ">":
			return RelationSymbol.GREATER;
		case "bvule":
			return RelationSymbol.BVULE;
		case "bvult":
			return RelationSymbol.BVULT;
		case "bvuge":
			return RelationSymbol.BVUGE;
		case "bvugt":
			return RelationSymbol.BVUGT;
		case "bvsle":
			return RelationSymbol.BVSLE;
		case "bvslt":
			return RelationSymbol.BVSLT;
		case "bvsge":
			return RelationSymbol.BVSGE;
		case "bvsgt":
			return RelationSymbol.BVSGT;
		default:
			return null;
		}
	}

	/**
	 * Given a relation symbol ▷, returns the relation symbol ◾ such that the relation ψ ◾ φ is equivalent to the
	 * negated relation ¬(ψ ▷ φ).
	 */
	public RelationSymbol negate() {
		final RelationSymbol result;
		switch (this) {
		case EQ:
			result = RelationSymbol.DISTINCT;
			break;
		case DISTINCT:
			result = RelationSymbol.EQ;
			break;
		case LEQ:
			result = RelationSymbol.GREATER;
			break;
		case GEQ:
			result = RelationSymbol.LESS;
			break;
		case LESS:
			result = RelationSymbol.GEQ;
			break;
		case GREATER:
			result = RelationSymbol.LEQ;
			break;
		case BVULE:
			result = RelationSymbol.BVUGT;
			break;
		case BVULT:
			result = RelationSymbol.BVUGE;
			break;
		case BVUGE:
			result = RelationSymbol.BVULT;
			break;
		case BVUGT:
			result = RelationSymbol.BVULE;
			break;
		case BVSLE:
			result = RelationSymbol.BVSGT;
			break;
		case BVSLT:
			result = RelationSymbol.BVSGE;
			break;
		case BVSGE:
			result = RelationSymbol.BVSLT;
			break;
		case BVSGT:
			result = RelationSymbol.BVSLE;
			break;
		default:
			throw new AssertionError("unknown RelationSymbol " + this);
		}
		return result;
	}

	/**
	 * Given a relation symbol ▷, returns the relation symbol ◾ such that the relation ψ ◾ φ is equivalent to the
	 * relation φ ▷ ψ, which is the relation where we swapped the parameters.
	 */
	public RelationSymbol swapParameters() {
		final RelationSymbol result;
		switch (this) {
		case EQ:
			result = RelationSymbol.EQ;
			break;
		case DISTINCT:
			result = RelationSymbol.DISTINCT;
			break;
		case LEQ:
			result = RelationSymbol.GEQ;
			break;
		case GEQ:
			result = RelationSymbol.LEQ;
			break;
		case LESS:
			result = RelationSymbol.GREATER;
			break;
		case GREATER:
			result = RelationSymbol.LESS;
			break;
		case BVULE:
			result = RelationSymbol.BVUGE;
			break;
		case BVULT:
			result = RelationSymbol.BVUGT;
			break;
		case BVUGE:
			result = RelationSymbol.BVULE;
			break;
		case BVUGT:
			result = RelationSymbol.BVULT;
			break;
		case BVSLE:
			result = RelationSymbol.BVSGE;
			break;
		case BVSLT:
			result = RelationSymbol.BVSGT;
			break;
		case BVSGE:
			result = RelationSymbol.BVSLE;
			break;
		case BVSGT:
			result = RelationSymbol.BVSLT;
			break;
		default:
			throw new AssertionError("unknown RelationSymbol " + this);
		}
		return result;
	}

	/**
	 * @return true iff the relation symbol is neither EQ nor DISTINCT. We call these inequalities "convex inequalities"
	 *         to emphasize that DISTINCT is not called an inequality.
	 */
	public boolean isConvexInequality() {
		final boolean result;
		switch (this) {
		case EQ:
		case DISTINCT:
			result = false;
			break;
		case LEQ:
		case GEQ:
		case LESS:
		case GREATER:
		case BVULE:
		case BVULT:
		case BVUGE:
		case BVUGT:
		case BVSLE:
		case BVSLT:
		case BVSGE:
		case BVSGT:
			result = true;
			break;
		default:
			throw new AssertionError("unknown RelationSymbol " + this);
		}
		return result;
	}

	public Term constructTerm(final Script script, final Term lhs, final Term rhs) {
		Term result;
		switch (this) {
		case EQ:
			result = CommuhashUtils.term(script, "=", null, null, lhs, rhs);
			break;
		case DISTINCT:
			result = SmtUtils.not(script, CommuhashUtils.term(script, "=", null, null, lhs, rhs));
			break;
		case LEQ:
			result = SmtUtils.leq(script, lhs, rhs);
			break;
		case GEQ:
			result = SmtUtils.leq(script, rhs, lhs);
			break;
		case LESS:
			result = SmtUtils.less(script, lhs, rhs);
			break;
		case GREATER:
			result = SmtUtils.less(script, rhs, lhs);
			break;
		case BVULE:
			result = SmtUtils.bvule(script, lhs, rhs);
			break;
		case BVULT:
			result = SmtUtils.bvult(script, lhs, rhs);
			break;
		case BVUGE:
			result = SmtUtils.bvule(script, lhs, rhs);
			break;
		case BVUGT:
			result = SmtUtils.bvult(script, lhs, rhs);
			break;
		case BVSLE:
			result = SmtUtils.bvsle(script, lhs, rhs);
			break;
		case BVSLT:
			result = SmtUtils.bvslt(script, lhs, rhs);
			break;
		case BVSGE:
			result = SmtUtils.bvsle(script, lhs, rhs);
			break;
		case BVSGT:
			result = SmtUtils.bvslt(script, lhs, rhs);
			break;
		default:
			throw new AssertionError("unknown RelationSymbol " + this);
		}
		return result;
	}

	public boolean isRelationSymbolGE() {
		if ((this == RelationSymbol.GEQ) || (this == RelationSymbol.BVUGE) || (this == RelationSymbol.BVSGE)) {
			return true;
		}
		return false;
	}

	public boolean isRelationSymbolLE() {
		if ((this == RelationSymbol.LEQ) || (this == RelationSymbol.BVULE) || (this == RelationSymbol.BVSLE)) {
			return true;
		}
		return false;
	}

	public boolean isRelationSymbolGT() {
		if ((this == RelationSymbol.GREATER) || (this == RelationSymbol.BVUGT) || (this == RelationSymbol.BVSGT)) {
			return true;
		}
		return false;
	}

	public boolean isRelationSymbolLT() {
		if ((this == RelationSymbol.LESS) || (this == RelationSymbol.BVULT) || (this == RelationSymbol.BVSLT)) {
			return true;
		}
		return false;
	}

	public RelationSymbol getNonStrictSymbol() {
		switch (this) {
		case EQ:
			return RelationSymbol.EQ;
		case DISTINCT:
			return RelationSymbol.DISTINCT;
		case LEQ:
			return RelationSymbol.LEQ;
		case GEQ:
			return RelationSymbol.GEQ;
		case LESS:
			return RelationSymbol.LEQ;
		case GREATER:
			return RelationSymbol.GEQ;
		case BVULE:
			return RelationSymbol.BVULE;
		case BVULT:
			return RelationSymbol.BVULE;
		case BVUGE:
			return RelationSymbol.BVUGE;
		case BVUGT:
			return RelationSymbol.BVUGE;
		case BVSLE:
			return RelationSymbol.BVSLE;
		case BVSLT:
			return RelationSymbol.BVSLE;
		case BVSGE:
			return RelationSymbol.BVSGE;
		case BVSGT:
			return RelationSymbol.BVSGE;
		default:
			throw new AssertionError("unknown RelationSymbol " + this);
		}
	}

	public RelationSymbol getStrictSymbol() {
		switch (this) {
		case EQ:
			return RelationSymbol.EQ;
		case DISTINCT:
			return RelationSymbol.DISTINCT;
		case LEQ:
			return RelationSymbol.LESS;
		case GEQ:
			return RelationSymbol.GREATER;
		case LESS:
			return RelationSymbol.LESS;
		case GREATER:
			return RelationSymbol.GREATER;
		case BVULE:
			return RelationSymbol.BVULT;
		case BVULT:
			return RelationSymbol.BVULT;
		case BVUGE:
			return RelationSymbol.BVUGT;
		case BVUGT:
			return RelationSymbol.BVUGT;
		case BVSLE:
			return RelationSymbol.BVSLT;
		case BVSLT:
			return RelationSymbol.BVSLT;
		case BVSGE:
			return RelationSymbol.BVSGT;
		case BVSGT:
			return RelationSymbol.BVSGT;
		default:
			throw new AssertionError("unknown RelationSymbol " + this);
		}
	}
}