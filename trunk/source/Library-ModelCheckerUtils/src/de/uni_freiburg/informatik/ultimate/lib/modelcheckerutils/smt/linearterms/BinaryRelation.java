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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms;

import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ContainsSubterm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Helper class that can be used to detect if a relation has certain form.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public abstract class BinaryRelation implements IBinaryRelation {

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
	}

	/**
	 * Given a relation symbol ▷, returns the relation symbol ◾ such that the relation ψ ◾ φ is equivalent to the
	 * relation ¬(ψ ▷ φ), which is the negated relation.
	 */
	public static RelationSymbol negateRelation(final RelationSymbol symb) {
		final RelationSymbol result;
		switch (symb) {
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
			throw new UnsupportedOperationException("unknown numeric relation");
		}
		return result;
	}

	/**
	 * Given a relation symbol ▷, returns the relation symbol ◾ such that the relation ψ ◾ φ is equivalent to the
	 * relation φ ▷ ψ, which is the relation where we swaped the parameters.
	 */
	public static RelationSymbol swapParameters(final RelationSymbol symb) {
		final RelationSymbol result;
		switch (symb) {
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
			throw new UnsupportedOperationException("unknown numeric relation");
		}
		return result;
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
		case LEQ:
		case LESS:
			result = toTerm(script, relationSymbol, lhsTerm, rhsTerm);
			break;
		case GEQ:
		case GREATER:
			final RelationSymbol swapped = BinaryRelation.swapParameters(relationSymbol);
			result = toTerm(script, swapped, rhsTerm, lhsTerm);
			break;
		default:
			throw new AssertionError("unknown relation symbol");
		}
		return result;
	}

	public Term toTerm(final Script script) {
		return toTerm(script, getRelationSymbol(), getLhs(), getRhs());
	}

	public static Term toTerm(final Script script, final RelationSymbol relationSymbol, final Term lhsTerm,
			final Term rhsTerm) {
		Term result;
		switch (relationSymbol) {
		case DISTINCT:
			final Term eq = script.term("=", lhsTerm, rhsTerm);
			result = script.term("not", eq);
			break;
		case EQ:
		case LEQ:
		case LESS:
		case GEQ:
		case GREATER:
			result = script.term(relationSymbol.toString(), lhsTerm, rhsTerm);
			break;
		default:
			throw new AssertionError("unknown relation symbol");
		}
		return result;
	}

	protected final RelationSymbol mRelationSymbol;
	protected final Term mLhs;
	protected final Term mRhs;

	protected BinaryRelation(final RelationSymbol relationSymbol, final Term lhs, final Term rhs) {
		super();
		mRelationSymbol = relationSymbol;
		mLhs = lhs;
		mRhs = rhs;
	}

	public BinaryRelation(final Term term) throws NoRelationOfThisKindException {
		if (!(term instanceof ApplicationTerm)) {
			throw new NoRelationOfThisKindException("no ApplicationTerm");
		}
		ApplicationTerm appTerm = (ApplicationTerm) term;
		String functionSymbolName = appTerm.getFunction().getName();
		Term[] params = appTerm.getParameters();
		boolean isNegated;
		if (functionSymbolName.equals("not")) {
			assert params.length == 1;
			final Term notTerm = params[0];
			if (!(notTerm instanceof ApplicationTerm)) {
				throw new NoRelationOfThisKindException("no ApplicationTerm");
			}
			isNegated = true;
			appTerm = (ApplicationTerm) notTerm;
			functionSymbolName = appTerm.getFunction().getName();
			params = appTerm.getParameters();
		} else {
			isNegated = false;
		}
		if (appTerm.getParameters().length != 2) {
			throw new NoRelationOfThisKindException("not binary");
		}
		checkSort(appTerm.getParameters());

		RelationSymbol relSymb = getRelationSymbol(functionSymbolName, isNegated);
		for (final RelationSymbol symb : RelationSymbol.values()) {
			if (symb.toString().equals(functionSymbolName)) {
				relSymb = isNegated ? negateRelation(symb) : symb;
				break;
			}
		}
		if (relSymb == null) {
			throw new NoRelationOfThisKindException("no binary numeric relation symbol");
		}
		mRelationSymbol = relSymb;
		mLhs = params[0];
		mRhs = params[1];
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

	@Override
	public SolvedBinaryRelation solveForSubject(final Script script, final Term subject) {
		if (getLhs().equals(subject)) {
			if (new ContainsSubterm(subject).containsSubterm(getRhs())) {
				return null;
			} else {
				return new SolvedBinaryRelation(subject, getRhs(), getRelationSymbol(), Collections.emptyMap());
			}
		} else if (getRhs().equals(subject)) {
			if (new ContainsSubterm(subject).containsSubterm(getLhs())) {
				return null;
			} else {
				return new SolvedBinaryRelation(subject, getLhs(), swapParameters(getRelationSymbol()),
						Collections.emptyMap());
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
