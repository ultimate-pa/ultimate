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

/**
 * Values of this enum represent the relation symbol of some binary relations.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public enum RelationSymbol {
	EQ("="), DISTINCT("distinct"), LEQ("<="), GEQ(">="), LESS("<"), GREATER(">");

	private final String mStringRepresentation;

	RelationSymbol(final String stringRepresentation) {
		mStringRepresentation = stringRepresentation;
	}

	@Override
	public String toString() {
		return mStringRepresentation;
	}

	/**
	 * @return {@link RelationSymbol} whose string representation is relAsString and
	 *         null if no {@link RelationSymbol} has such a string representation.
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
		default:
			throw new AssertionError("unknown RelationSymbol " + this);
		}
		return result;
	}
}