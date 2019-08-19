/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Represents an term of the form ψ ▷ φ, where ψ and φ are
 * {@link AffineTerm}s and ▷ is a binary relation symbol from the following
 * list.
 * <p>
 * ▷ ∈ { =, !=, \<=, \<, \>=, \> }
 * </p>
 * <p>
 * Allows to return this relation as an SMT term in the following two forms:
 * <ul>
 * <li>positive normal form
 * <li>the form where a specific variable is on the left hand side and all other
 * summands are moved to the right hand side.
 * </ul>
 * </p>
 *
 * @author Matthias Heizmann, Max Barth
 */
public class AffineRelation extends AbstractGeneralizedaAffineRelation<AffineTerm, Term> {

	public AffineRelation(final Script script, final AffineTerm term, final RelationSymbol relationSymbol) {
		super(script, term, relationSymbol);
	}

	public AffineRelation(final Script script, final TransformInequality transformInequality,
			final RelationSymbol relationSymbol, final AffineTerm affineLhs, final AffineTerm affineRhs,
			final Term term) {
		super(script, transformInequality, relationSymbol, affineLhs, affineRhs, term);
	}

	static AffineTerm transformToAffineTerm(final Script script, final Term term) {
		if (TEMPORARY_POLYNOMIAL_TERM_TEST) {
			final IPolynomialTerm polynomialTerm = (IPolynomialTerm) new PolynomialTermTransformer(script)
					.transform(term);
			final Term toTerm = polynomialTerm.toTerm(script);
			final LBool lbool = Util.checkSat(script, script.term("distinct", term, toTerm));
			if (lbool != LBool.UNSAT) {
				throw new AssertionError(
						"Input and output is not equivalent (" + lbool + "). Input: " + term + " Output: " + toTerm);
			}
		}
		return (AffineTerm) new AffineTermTransformer(script).transform(term);
	}

	@Override
	protected AffineTerm sum(final AffineTerm op1, final AffineTerm op2) {
		return AffineTerm.sum(op1, op2);
	}

	@Override
	protected AffineTerm mul(final AffineTerm op, final Rational r) {
		return AffineTerm.mul(op, r);
	}

	@Override
	protected AffineTerm constructConstant(final Sort s, final Rational r) {
		return AffineTerm.constructConstant(s, r);
	}

	public static AffineRelation convert(final Script script, final Term term) {
		return convert(script, term, TransformInequality.NO_TRANFORMATION);
	}

	@Override
	protected Term getTheAbstractVarOfSubject(final Term subject) {
		boolean subjectOccurred = false;
		for (final Term concreteVar : mAffineTerm.getVariable2Coefficient().keySet()) {
			if (concreteVar == subject) {
				subjectOccurred = true;
			} else {
				final boolean subjectOccursAsSubterm = new SubtermPropertyChecker(x -> x == subject)
						.isPropertySatisfied(concreteVar);
				if (subjectOccursAsSubterm) {
					return null;
				}
			}
		}
		if (!subjectOccurred) {
			throw new AssertionError("superclass already chekced that subject is abstract var");
		}
		return subject;
	}

	public static AffineRelation convert(final Script script, final Term term,
			final TransformInequality transformInequality) {
		final BinaryNumericRelation bnr = BinaryNumericRelation.convert(term);
		if (bnr == null) {
			return null;
		}
		final Term lhs = bnr.getLhs();
		final Term rhs = bnr.getRhs();
		final AffineTerm affineLhs = transformToAffineTerm(script, lhs);
		final AffineTerm affineRhs = transformToAffineTerm(script, rhs);
		if (affineLhs.isErrorTerm() || affineRhs.isErrorTerm()) {
			return null;
		}
		final RelationSymbol relationSymbol = bnr.getRelationSymbol();
		return new AffineRelation(script, transformInequality, relationSymbol, affineLhs, affineRhs, term);
	}

}
