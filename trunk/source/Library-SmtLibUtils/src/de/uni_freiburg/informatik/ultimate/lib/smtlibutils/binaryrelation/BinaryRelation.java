/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Helper class that can be used to detect if a relation has certain form.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public abstract class BinaryRelation implements IBinaryRelation {

	protected final RelationSymbol mRelationSymbol;
	protected final Term mLhs;
	protected final Term mRhs;

	protected BinaryRelation(final RelationSymbol relationSymbol, final Term lhs, final Term rhs) {
		super();
		mRelationSymbol = relationSymbol;
		mLhs = lhs;
		mRhs = rhs;
	}

	public RelationSymbol getRelationSymbol() {
		return mRelationSymbol;
	}

	public Term getLhs() {
		return mLhs;
	}

	public Term getRhs() {
		return mRhs;
	}

	/**
	 * Returns the term (relationSymbol lhsTerm rhsTerm) if relationSymbol is not a
	 * greater-than relation symbol. Otherwise returns an equivalent term where
	 * relation symbol and parameters are swapped.
	 */
	public static Term constructLessNormalForm(final Script script, final RelationSymbol relationSymbol,
			final Term lhsTerm, final Term rhsTerm) throws AssertionError {
		final Term result;

		switch (relationSymbol) {
		case DISTINCT:
		case EQ:
			// make sure that result respects the {@link CommuhashNormalForm}
			final Term[] sortedOperands = CommuhashUtils.sortByHashCode(lhsTerm, rhsTerm);
			result = toTerm(script, relationSymbol, sortedOperands[0], sortedOperands[1]);
			break;
		case BVULE:
		case BVULT:
		case BVSLE:
		case BVSLT:
		case LEQ:
		case LESS:
			result = toTerm(script, relationSymbol, lhsTerm, rhsTerm);
			break;
		case BVUGE:
		case BVUGT:
		case BVSGE:
		case BVSGT:
		case GEQ:
		case GREATER:
			final RelationSymbol swapped = relationSymbol.swapParameters();
			result = toTerm(script, swapped, rhsTerm, lhsTerm);
			break;
		default:
			throw new AssertionError("unknown relation symbol");
		}
		return result;
	}

	public Term toTerm(final Script script) {
		return constructLessNormalForm(script, getRelationSymbol(), getLhs(), getRhs());
	}

	public static Term toTerm(final Script script, final RelationSymbol relationSymbol, final Term lhsTerm,
			final Term rhsTerm) {
		Term result;
		switch (relationSymbol) {
		case DISTINCT:
			final Term eq = SmtUtils.binaryEquality(script, lhsTerm, rhsTerm);
			result = script.term("not", eq);
			break;
		case EQ:
		case LEQ:
		case LESS:
		case GEQ:
		case GREATER:
		case BVULE:
		case BVULT:
		case BVUGE:
		case BVUGT:
		case BVSLE:
		case BVSLT:
		case BVSGE:
		case BVSGT:
			result = script.term(relationSymbol.toString(), lhsTerm, rhsTerm);
			break;
		default:
			throw new AssertionError("unknown relation symbol");
		}
		return result;
	}

	@Override
	public SolvedBinaryRelation solveForSubject(final Script script, final Term subject) {
		if (getLhs().equals(subject)) {
			if (SmtUtils.isSubterm(getRhs(), subject)) {
				return null;
			} else {
				return new SolvedBinaryRelation(subject, getRhs(), getRelationSymbol());
			}
		} else if (getRhs().equals(subject)) {
			if (SmtUtils.isSubterm(getLhs(), subject)) {
				return null;
			} else {
				return new SolvedBinaryRelation(subject, getLhs(), getRelationSymbol().swapParameters());
			}
		} else {
			return null;
		}
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mLhs == null) ? 0 : mLhs.hashCode());
		// Enums in Java do not have a "stable" hashCode the hashCode varies between
		// different runs. Furthermore, we cannot overwrite the hashCode method of an
		// enum. Hence we do not use the mRelationSymbol's hashCode but the hashCode
		// of its string representation.
		result = prime * result + ((mRelationSymbol == null) ? 0 : mRelationSymbol.toString().hashCode());
		result = prime * result + ((mRhs == null) ? 0 : mRhs.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		final BinaryRelation other = (BinaryRelation) obj;
		if (mLhs == null) {
			if (other.mLhs != null)
				return false;
		} else if (!mLhs.equals(other.mLhs))
			return false;
		if (mRelationSymbol != other.mRelationSymbol)
			return false;
		if (mRhs == null) {
			if (other.mRhs != null)
				return false;
		} else if (!mRhs.equals(other.mRhs))
			return false;
		return true;
	}



}
