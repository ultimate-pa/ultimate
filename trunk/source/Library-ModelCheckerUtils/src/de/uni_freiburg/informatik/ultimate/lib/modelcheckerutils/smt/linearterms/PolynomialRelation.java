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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms;

import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AbstractGeneralizedAffineRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;


/**
 * Represents an term of the form ψ ▷ φ, where ψ and φ are
 * {@link PolynomialTerm}s or {@link AffineTerm}s and ▷ is a binary relation symbol 
 * from the following list.
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
 * @author Leonard Fichtner
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class PolynomialRelation extends AbstractGeneralizedAffineRelation<AbstractGeneralizedAffineTerm<Term>, Term> {

	public PolynomialRelation(final Script script, final AbstractGeneralizedAffineTerm<?> term, final RelationSymbol relationSymbol) {
		super(script, checkThenCast(term), relationSymbol);
	}
	
	public PolynomialRelation(final Script script, final TransformInequality transformInequality,
			final RelationSymbol relationSymbol, final AbstractGeneralizedAffineTerm<?> polyLhs, 
			final AbstractGeneralizedAffineTerm<?> polyRhs, final Term term) {
		super(script, transformInequality, relationSymbol, checkThenCast(polyLhs), checkThenCast(polyRhs), term);
	}

	/**
	 * Given a AbstractGeneralizedAffineTerm, check whether it is of Type AffineTerm and PolynomialTerm.
	 * If yes, cast it (UNSAFE) and return the result, throw an exception otherwise.
	 */
	private static AbstractGeneralizedAffineTerm<Term> checkThenCast(AbstractGeneralizedAffineTerm<?> poly){
		if (!(poly instanceof AffineTerm || poly instanceof PolynomialTerm)) {
			throw new IllegalArgumentException("PolynomialRelation accepts only AffineTerm and PolynomialTerm as internal terms.");
		}
		return unsafeCast(poly);
	}
	
	@SuppressWarnings("unchecked")
	private static AbstractGeneralizedAffineTerm<Term> unsafeCast(AbstractGeneralizedAffineTerm<?> poly) {
		return (AbstractGeneralizedAffineTerm<Term>) poly;
	}

	@Override
	protected AbstractGeneralizedAffineTerm<Term> sum(final AbstractGeneralizedAffineTerm<Term> op1, final AbstractGeneralizedAffineTerm<Term> op2) {
		final AbstractGeneralizedAffineTerm<Term> result;
		if (op1.isAffine() && op2.isAffine()) {
			result = AffineTerm.sum(op1, op2);
		} else {
			final AbstractGeneralizedAffineTerm<?> polynomialSum = PolynomialTerm.sum(op1, op2);
			result = unsafeCast(polynomialSum);
		}
		return result;
	}

	@Override
	protected AbstractGeneralizedAffineTerm<Term> mul(final AbstractGeneralizedAffineTerm<Term> op, final Rational r) {
		final AbstractGeneralizedAffineTerm<Term> result;
		if (op.isAffine()) {
			result = AffineTerm.mul(op, r);
		} else {
			final AbstractGeneralizedAffineTerm<?> polynomialSum = PolynomialTerm.mul(op, r);
			result = unsafeCast(polynomialSum);
		}
		return result;
	}

	@Override
	protected AffineTerm constructConstant(final Sort s, final Rational r) {
		return AffineTerm.constructConstant(s, r);
	}

	@Override
	protected Term getTheAbstractVarOfSubject(final Term subject) {
		if (mAffineTerm.isAffine()) {
			return getVarOfSubject(subject);
		}else {
			return getMonomialOfSubject(subject);
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
		return abstractVarOfSubject;
	}

	public static PolynomialRelation convert(final Script script, final Term term) {
		return convert(script, term, TransformInequality.NO_TRANFORMATION);
	}
	
	public static PolynomialRelation convert(final Script script, final Term term,
			final TransformInequality transformInequality) {
		final BinaryNumericRelation bnr = BinaryNumericRelation.convert(term);
		if (bnr == null) {
			return null;
		}
		final Term lhs = bnr.getLhs();
		final Term rhs = bnr.getRhs();
		final AbstractGeneralizedAffineTerm<?> polyLhs = transformToPolynomialTerm(script, lhs);
		final AbstractGeneralizedAffineTerm<?> polyRhs = transformToPolynomialTerm(script, rhs);
		if (polyLhs.isErrorTerm() || polyRhs.isErrorTerm()) {
			return null;
		}
		final RelationSymbol relationSymbol = bnr.getRelationSymbol();
		return new PolynomialRelation(script, transformInequality, relationSymbol, polyLhs, polyRhs, term);
	}

	static AbstractGeneralizedAffineTerm<?> transformToPolynomialTerm(final Script script, final Term term) {
		return (AbstractGeneralizedAffineTerm<?>) new PolynomialTermTransformer(script).transform(term);
	}

}
