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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;


/**
 *
 * @author Leonard Fichtner
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class PolynomialRelation extends AbstractGeneralizedaAffineRelation<AbstractGeneralizedAffineTerm<Term>, Term> {

	//TODO: Ask Matthias whether really only AffineTerm is allowed in the constructors.
	public PolynomialRelation(final Script script, final AffineTerm term, final RelationSymbol relationSymbol) {
		super(script, term, relationSymbol);
	}

	public PolynomialRelation(final Script script, final TransformInequality transformInequality,
			final RelationSymbol relationSymbol, final AffineTerm affineLhs, final AffineTerm affineRhs,
			final Term term) {
		super(script, transformInequality, relationSymbol, affineLhs, affineRhs, term);
	}

//	static AffineTerm transformToAffineTerm(final Script script, final Term term) {
//		return (AffineTerm) new AffineTermTransformer(script).transform(term);
//	}

	@Override
	protected AbstractGeneralizedAffineTerm<Term> sum(final AbstractGeneralizedAffineTerm<Term> op1, final AbstractGeneralizedAffineTerm<Term> op2) {
		final AbstractGeneralizedAffineTerm<Term> result;
		if (op1.isAffine() && op2.isAffine()) {
			result = AffineTerm.sum(op1, op2);
		} else {
			final AbstractGeneralizedAffineTerm<?> polynomialSum = PolynomialTerm.sum(op1, op2);
			result = (AbstractGeneralizedAffineTerm<Term>) polynomialSum;
		}
		return result;
	}

	@Override
	protected AbstractGeneralizedAffineTerm<Term> mul(final AbstractGeneralizedAffineTerm<Term> op, final Rational r) {
		return AffineTerm.mul(op, r);
	}

	@Override
	protected AffineTerm constructConstant(final Sort s, final Rational r) {
		return AffineTerm.constructConstant(s, r);
	}

//	public static PolynomialRelation convert(final Script script, final Term term) {
//		return convert(script, term, TransformInequality.NO_TRANFORMATION);
//	}

	@Override
	protected Term getTheAbstractVarOfSubject(final Term subject) {
		if (mAffineTerm.isAffine()) {
			return getMonomialOfSubject(subject);
		}else {
			return getVarOfSubject(subject);
		}
	}

	/**
	 * This implements getAbstractVarOfSubject in case that this Relation represents a truly polynomial relation.
	 */
	private Term getMonomialOfSubject(final Term subject) {
		boolean subjectOccurred = false;
		Term abstractVarOfSubject = null;
		for (final Term concreteVar : mAffineTerm.getAbstractVariable2Coefficient().keySet()) {
			for (final Entry<Term, Rational> var2exp : ((Monomial) concreteVar).getVariable2Exponent().entrySet()) {
				if (var2exp.getKey() == subject) {
					//TODO: Ask Matthias about higher exponents of variables
					if (var2exp.getValue() != Rational.ONE || subjectOccurred) {
						return null;
					}else {
						subjectOccurred = true;
						abstractVarOfSubject = concreteVar;
					}
				}else {
					final boolean subjectOccursAsSubterm = new SubtermPropertyChecker(x -> x == subject)
							.isPropertySatisfied(var2exp.getKey());
					if (subjectOccursAsSubterm) {
						return null;
					}
				}
			}
		}
		if (!subjectOccurred) {
			throw new AssertionError("superclass already checked that subject is abstract var");
		}
		if (abstractVarOfSubject == null) {
			throw new AssertionError("abstractVarOfSubject must always be assigned, when the subject occurs!");
		}
		return abstractVarOfSubject;
	}

	/**
	 * This implements getAbstractVarOfSubject in case that this is an affine Relation.
	 */
	private Term getVarOfSubject(final Term subject) {
		boolean subjectOccurred = false;
		Term abstractVarOfSubject = null;
		for (final Term concreteVar : mAffineTerm.getAbstractVariable2Coefficient().keySet()) {
			if (concreteVar == subject) {
				subjectOccurred = true;
				abstractVarOfSubject = concreteVar;
			} else {
				final boolean subjectOccursAsSubterm = new SubtermPropertyChecker(x -> x == subject)
						.isPropertySatisfied(concreteVar);
				if (subjectOccursAsSubterm) {
					return null;
				}
			}
		}
		if (!subjectOccurred) {
			throw new AssertionError("superclass already checked that subject is abstract var");
		}
		if (abstractVarOfSubject == null) {
			throw new AssertionError("abstractVarOfSubject must always be assigned, when the subject occurs!");
		}
		return abstractVarOfSubject;
	}

//	public static PolynomialRelation convert(final Script script, final Term term,
//			final TransformInequality transformInequality) {
//		final BinaryNumericRelation bnr = BinaryNumericRelation.convert(term);
//		if (bnr == null) {
//			return null;
//		}
//		final Term lhs = bnr.getLhs();
//		final Term rhs = bnr.getRhs();
//		final AffineTerm affineLhs = transformToAffineTerm(script, lhs);
//		final AffineTerm affineRhs = transformToAffineTerm(script, rhs);
//		if (affineLhs.isErrorTerm() || affineRhs.isErrorTerm()) {
//			return null;
//		}
//		final RelationSymbol relationSymbol = bnr.getRelationSymbol();
//		return new PolynomialRelation(script, transformInequality, relationSymbol, affineLhs, affineRhs, term);
//	}

}
