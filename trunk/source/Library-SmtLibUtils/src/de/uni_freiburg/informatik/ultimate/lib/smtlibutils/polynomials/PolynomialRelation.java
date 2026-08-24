/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.IBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.DualJunctionTir;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Represents a term of the form &psi; &#9657; &phi;, where &psi; and &phi; are polynomial terms and &#9657; is a
 * binary relation symbol, either one of {@code = != <= < >= >} or one of the eight bitvector inequality symbols.
 * <p>
 * There are two implementations of this interface:
 * <ul>
 * <li>{@link SingleTermPolynomialRelation} - the original representation. Reduces the relation to a single
 * polynomial term compared against zero (&psi; &#9657; 0, where &psi; = lhs - rhs). Sound for Int/Real inequalities
 * and for equalities of any sort, including bitvectors.
 * <li>{@link TwoSidedPolynomialRelation} - keeps the left-hand side and right-hand side as two separate polynomial
 * terms, never combined via subtraction. Needed for bitvector inequalities, where reducing to a single term compared
 * against zero is unsound under two's-complement wraparound.
 * </ul>
 * </p>
 *
 * @author Leonard Fichtner
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public interface PolynomialRelation extends IBinaryRelation, ITermProvider {

	enum TransformInequality {
		NO_TRANFORMATION, STRICT2NONSTRICT, NONSTRICT2STRICT;

		/**
		 * For the TIR quantifier elimination technique (see {@link DualJunctionTir}), we prefer non-strict
		 * inequalities for the existential quantifier and we prefer strict inequalities for the universal
		 * quantifier.
		 */
		static TransformInequality determineTransformationForTir(final int quantifier) {
			TransformInequality result;
			if (quantifier == QuantifiedFormula.EXISTS) {
				result = TransformInequality.STRICT2NONSTRICT;
			} else if (quantifier == QuantifiedFormula.FORALL) {
				result = TransformInequality.NONSTRICT2STRICT;
			} else {
				throw new AssertionError("Unknown quantifier");
			}
			return result;
		}
	}

	enum TrivialityStatus {
		EQUIVALENT_TO_TRUE, EQUIVALENT_TO_FALSE, NONTRIVIAL
	}

	// --- static factories ---
	// Unchanged behavior for now: always delegate to SingleTermPolynomialRelation, exactly like before this
	// interface existed (including still returning null for bitvector inequalities).
	// TODO: once TwoSidedPolynomialRelation is functional, these need to detect bitvector inequalities and route
	// to TwoSidedPolynomialRelation.of(...) instead. Deliberately left alone for now, so nothing that currently
	// relies on the existing "returns null for bv inequalities" behavior (e.g. UnfTransformer's null-check) breaks.

	static PolynomialRelation of(final AbstractGeneralizedAffineTerm<?> agat, final RelationSymbol relationSymbol) {
		return SingleTermPolynomialRelation.of(agat, relationSymbol);
	}

	static PolynomialRelation of(final Script script, final Term term) {
		return SingleTermPolynomialRelation.of(script, term);
	}

	static PolynomialRelation of(final Script script, final Term term,
			final TransformInequality transformInequality) {
		return SingleTermPolynomialRelation.of(script, term, transformInequality);
	}

	static PolynomialRelation of(final Script script, final RelationSymbol relationSymbol, final Term lhs,
			final Term rhs) {
		return SingleTermPolynomialRelation.of(script, relationSymbol, lhs, rhs);
	}

	static PolynomialRelation of(final TransformInequality transformInequality, final RelationSymbol relationSymbol,
			final AbstractGeneralizedAffineTerm<?> polyLhs, final AbstractGeneralizedAffineTerm<?> polyRhs) {
		return SingleTermPolynomialRelation.of(transformInequality, relationSymbol, polyLhs, polyRhs);
	}

	// --- instance methods ---

	RelationSymbol getRelationSymbol();

	/**
	 * @return the single polynomial term &psi; such that &psi; &#9657; 0 is equivalent to this relation.
	 *         TODO: only meaningful for {@link SingleTermPolynomialRelation} - a two-sided relation has no single
	 *         such term. Kept on this interface only because {@link ExplicitLhsPolynomialRelation} and
	 *         {@link PolyPoNeWithContext} already call it on values statically typed as {@link PolynomialRelation}.
	 */
	AbstractGeneralizedAffineTerm<?> getPolynomialTerm();

	@Override
	Term toTerm(Script script);

	@Override
	SolvedBinaryRelation solveForSubject(Script script, Term subject);

	/**
	 * TODO: needs real design work for {@link TwoSidedPolynomialRelation} - solving for a subject means moving
	 * terms across the relation, which is exactly the operation that's unsafe for bitvectors under wraparound.
	 */
	MultiCaseSolvedBinaryRelation solveForSubject(ManagedScript mgdScript, Term subject,
			MultiCaseSolvedBinaryRelation.Xnf xnf, Set<TermVariable> bannedForDivCapture,
			boolean allowDivModBasedSolution);

	boolean isAffine();

	boolean isVariable(Term var);

	PolynomialRelation negate();

	/**
	 * TODO: needs real design work for {@link TwoSidedPolynomialRelation} - multiplying a bitvector relation by a
	 * constant involves bitvector multiplication, which wraps too, so this needs the same careful treatment as
	 * {@link #solveForSubject}.
	 */
	PolynomialRelation mul(Script script, Rational r);

	SolvedBinaryRelation isSimpleEquality(Script script);

	PolynomialRelation tryToConvertToEquivalentNonStrictRelation();

}
