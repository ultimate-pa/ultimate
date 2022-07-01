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

	/**
	 * Check if Sort of parameters is compatible. Throw Exception if not.
	 *
	 * @throws NoRelationOfThisKindException
	 */
	abstract protected void checkSort(Term[] params) throws NoRelationOfThisKindException;

	/**
	 * Return the RelationSymbol for this relation resolve negation
	 *
	 * @param functionSymbolName
	 *            function symbol name of the original term
	 * @param isNegated
	 *            true iff the original term is negated
	 * @throws NoRelationOfThisKindException
	 */
	abstract protected RelationSymbol getRelationSymbol(String functionSymbolName, boolean isNegated)
			throws NoRelationOfThisKindException;

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
	 * Returns the term (relationSymbol lhsTerm rhsTerm) if relationSymbol is not a greater-than relation symbol.
	 * Otherwise returns an equivalent term where relation symbol and parameters are swapped.
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

	public static class NoRelationOfThisKindException extends Exception {

		private static final long serialVersionUID = 1L;

		public NoRelationOfThisKindException(final String message) {
			super(message);
		}
	}

}
