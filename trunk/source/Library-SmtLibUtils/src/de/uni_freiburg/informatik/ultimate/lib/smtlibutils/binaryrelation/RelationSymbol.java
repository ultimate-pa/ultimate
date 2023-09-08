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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Values of this enum represent the relation symbol of some binary relations.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */

public enum RelationSymbol {
	EQ("="), DISTINCT("distinct"), LEQ("<="), GEQ(">="), LESS("<"), GREATER(">"), BVULE("bvule"), BVULT("bvult"),
	BVUGE("bvuge"), BVUGT("bvugt"), BVSLE("bvsle"), BVSLT("bvslt"), BVSGE("bvsge"), BVSGT("bvsgt");

	private final String mStringRepresentation;

	RelationSymbol(final String stringRepresentation) {
		mStringRepresentation = stringRepresentation;
	}

	public enum BvSignedness {
		SIGNED, UNSIGNED
	}

	@Override
	public String toString() {
		return mStringRepresentation;
	}

	/**
	 * @return {@link RelationSymbol} whose string representation is relAsString
	 *         and null if no {@link RelationSymbol} has such a string
	 *         representation.
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
	 * Given a relation symbol ▷, returns the relation symbol ◾ such that the
	 * relation ψ ◾ φ is equivalent to the negated relation ¬(ψ ▷ φ).
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
	 * Given a relation symbol ▷, returns the relation symbol ◾ such that the
	 * relation ψ ◾ φ is equivalent to the relation φ ▷ ψ, which is the relation
	 * where we swapped the parameters.
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
	 * @return true iff the relation symbol is neither EQ nor DISTINCT. We call
	 *         these inequalities "convex inequalities" to emphasize that
	 *         DISTINCT is not called an inequality.
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
			result = SmtUtils.bvule(script, rhs, lhs);
			break;
		case BVUGT:
			result = SmtUtils.bvult(script, rhs, lhs);
			break;
		case BVSLE:
			result = SmtUtils.bvsle(script, lhs, rhs);
			break;
		case BVSLT:
			result = SmtUtils.bvslt(script, lhs, rhs);
			break;
		case BVSGE:
			result = SmtUtils.bvsle(script, rhs, lhs);
			break;
		case BVSGT:
			result = SmtUtils.bvslt(script, rhs, lhs);
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

	public boolean isStrictRelation() {
		switch (this) {
		case EQ:
		case DISTINCT:
		case LEQ:
		case GEQ:
		case BVULE:
		case BVUGE:
		case BVSGE:
		case BVSLE:
			return false;
		case LESS:
		case GREATER:
		case BVULT:
		case BVUGT:
		case BVSLT:
		case BVSGT:
			return true;
		default:
			throw new AssertionError("unknown RelationSymbol " + this);
		}
	}

	/**
	 * If this is a non-strict inequality then return the corresponding strict inequality symbol.
	 * Otherwise, return this.
	 */
	public RelationSymbol getCorrespondingStrictRelationSymbol() {
		switch (this) {
		case LEQ:
			return LESS;
		case GEQ:
			return GREATER;
		case BVULE:
			return BVULT;
		case BVUGE:
			return BVUGT;
		case BVSGE:
			return BVSGT;
		case BVSLE:
			return BVSLT;
		case EQ:
		case DISTINCT:
		case LESS:
		case GREATER:
		case BVULT:
		case BVUGT:
		case BVSLT:
		case BVSGT:
			return this;
		default:
			throw new AssertionError("unknown RelationSymbol " + this);
		}
	}

	/**
	 * Let `ψ ▷ 0` be a polynomial relation whose sort is `Int`. Which offset δ do
	 * we have to add such that the relation `ψ + δ ▶ 0` in which ▶is the strict
	 * version of ▷(if available) is equivalent to the original relation.
	 */
	public Rational getOffsetForNonstrictToStrictTransformation() {
		switch (this) {
		case LEQ:
			return Rational.MONE;
		case GEQ:
			return Rational.ONE;
		case EQ:
		case DISTINCT:
		case LESS:
		case GREATER:
			return Rational.ZERO;
		case BVULE:
		case BVUGE:
		case BVSGE:
		case BVSLE:
		case BVULT:
		case BVUGT:
		case BVSLT:
		case BVSGT:
			throw new AssertionError("Non-strict to strict transformation not available for bitvectors");
		default:
			throw new AssertionError("unknown RelationSymbol " + this);
		}
	}

	public RelationSymbol getCorrespondingNonStrictRelationSymbol() {
		switch (this) {
		case LESS:
			return LEQ;
		case GREATER:
			return GEQ;
		case BVULT:
			return BVULE;
		case BVUGT:
			return BVUGE;
		case BVSLT:
			return BVSLE;
		case BVSGT:
			return BVSGE;
		case LEQ:
		case GEQ:
		case BVULE:
		case BVUGE:
		case BVSGE:
		case BVSLE:
		case EQ:
		case DISTINCT:
			return this;
		default:
			throw new AssertionError("unknown RelationSymbol " + this);
		}
	}

	/**
	 * Let `ψ ▷ 0` be a polynomial relation whose sort is `Int`. Which offset δ do
	 * we have to add such that the relation `ψ + δ ▶ 0` in which ▶is the non-strict
	 * version of ▷(if available) is equivalent to the original relation.
	 */
	public Rational getOffsetForStrictToNonstrictTransformation() {
		switch (this) {
		case LESS:
			return Rational.ONE;
		case GREATER:
			return Rational.MONE;
		case EQ:
		case DISTINCT:
		case LEQ:
		case GEQ:
			return Rational.ZERO;
		case BVULE:
		case BVUGE:
		case BVSGE:
		case BVSLE:
		case BVULT:
		case BVUGT:
		case BVSLT:
		case BVSGT:
			throw new AssertionError("Strict to non-strict transformation not available for bitvectors");
		default:
			throw new AssertionError("unknown RelationSymbol " + this);
		}
	}


	public static RelationSymbol getLessRelationSymbol(final boolean strict, final Sort sort,
			final BvSignedness sigedness) {
		final RelationSymbol result;
		if (SmtSortUtils.isBitvecSort(sort)) {
			if (strict) {
				switch (sigedness) {
				case SIGNED:
					result = BVSLT;
					break;
				case UNSIGNED:
					result = BVULT;
					break;
				default:
					throw new AssertionError("unknown value " + sigedness);
				}
			} else {
				switch (sigedness) {
				case SIGNED:
					result = BVSLE;
					break;
				case UNSIGNED:
					result = BVULE;
					break;
				default:
					throw new AssertionError("unknown value " + sigedness);
				}
			}
		} else {
			if (strict) {
				result = LESS;
			} else {
				result = LEQ;
			}
		}
		return result;
	}

	public static RelationSymbol getGreaterRelationSymbol(final boolean strict, final Sort sort,
			final BvSignedness sigedness) {
		final RelationSymbol result;
		if (SmtSortUtils.isBitvecSort(sort)) {
			if (strict) {
				switch (sigedness) {
				case SIGNED:
					result = BVSGT;
					break;
				case UNSIGNED:
					result = BVUGT;
					break;
				default:
					throw new AssertionError("unknown value " + sigedness);
				}
			} else {
				switch (sigedness) {
				case SIGNED:
					result = BVSGE;
					break;
				case UNSIGNED:
					result = BVUGE;
					break;
				default:
					throw new AssertionError("unknown value " + sigedness);
				}
			}
		} else {
			if (strict) {
				result = GREATER;
			} else {
				result = GEQ;
			}
		}
		return result;
	}

	public boolean isSignedBvRelation() {
		switch (this) {
		case EQ:
		case DISTINCT:
		case LEQ:
		case GEQ:
		case LESS:
		case GREATER:
		case BVULE:
		case BVULT:
		case BVUGE:
		case BVUGT:
			return false;
		case BVSLE:
		case BVSLT:
		case BVSGE:
		case BVSGT:
			return true;
		default:
			throw new AssertionError("unknown RelationSymbol " + this);
		}
	}

	public boolean isUnSignedBvRelation() {
		switch (this) {
		case EQ:
		case DISTINCT:
		case LEQ:
		case GEQ:
		case LESS:
		case GREATER:
		case BVSLE:
		case BVSLT:
		case BVSGE:
		case BVSGT:
			return false;
		case BVULE:
		case BVULT:
		case BVUGE:
		case BVUGT:
			return true;
		default:
			throw new AssertionError("unknown RelationSymbol " + this);
		}
	}

	public BvSignedness getSignedness() {
		switch(this) {
		case BVSGE:
		case BVSGT:
		case BVSLE:
		case BVSLT:
			return BvSignedness.SIGNED;
		case BVUGE:
		case BVUGT:
		case BVULE:
		case BVULT:
			return BvSignedness.UNSIGNED;
		default:
			throw new AssertionError("not a bitvector inequality " + this);
		}
	}
}