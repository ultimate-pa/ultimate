/*
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import java.math.BigInteger;
import java.util.Collections;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.PolynomialTermUtils.GeneralizedConstructor;

/**
 * This represents an affine term in the form of
 *
 * <pre>
 * Σ c_i * x_i + c,
 * </pre>
 *
 * where c_i, c are literals and x_i are variables. We consider every term as a variable unless is is an
 * {@link ApplicationTerm} whose {@link FunctionSymbol} is an "affine symbol"
 * {@link AffineTermTransformer#isAffineSymbol}. Hence variables are e.g., {@link TermVariable}, constants (i.e., 0-ary
 * function symbols), function applications, array read expressions (i.e., select terms)
 * <p>
 * Note that this class extends {@link Term} but it is not supported by the solver. We extend Term only that this can be
 * returned by a TermTransformer.
 * </p>
 * <p>
 * Note that there is a class (@link de.uni_freiburg.informatik.ultimate.smtinterpol.convert.AffineTerm} which is
 * somehow similar but we cannot extend it because it too closely interweaved with the SMTInterpol.
 * </p>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Jan Leike
 */
public class AffineTerm extends AbstractGeneralizedAffineTerm<Term> {

	public AffineTerm() {
		super();
	}

	/**
	 * Constructor to be used of all static methods that construct an affineTerm.
	 */
	AffineTerm(final Sort s, final Rational constant, final Map<Term, Rational> variables2coeffcient) {
		super(s, constant, variables2coeffcient);
	}

	/**
	 * @returns {@link AffineTerm} that has sort s and represents a Term of the given {@link Rational} value.
	 */
	public static AffineTerm constructConstant(final Sort s, final Rational constant) {
		return new AffineTerm(s, constant, Collections.emptyMap());
	}

	/**
	 * {@link AffineTerm} that consists of the single variable that is represented by the {@link Term} t.
	 */
	public static AffineTerm constructVariable(final Term t) {
		return new AffineTerm(t.getSort(), Rational.ZERO, Collections.singletonMap(t, Rational.ONE));
	}

	static AffineTerm sum(final IPolynomialTerm... summands) {
		final GeneralizedConstructor<Term, AffineTerm> constructor = AffineTerm::new;
		return PolynomialTermUtils.constructSum(x -> ((AffineTerm) x).getVariable2Coefficient(), constructor, summands);
	}

	/**
	 * @returns AffineTerm that represents the product of affineTerm and multiplier.
	 */
	public static AffineTerm mul(final IPolynomialTerm affineTerm, final Rational multiplier) {
		final GeneralizedConstructor<Term, AffineTerm> constructor = AffineTerm::new;
		return PolynomialTermUtils.constructMul(x -> ((AffineTerm) x).getVariable2Coefficient(), constructor,
				affineTerm, multiplier);
	}

	public static AffineTerm mulAffineTerms(final IPolynomialTerm poly1, final IPolynomialTerm poly2) {
		if (poly1.isConstant()) {
			return mul(poly2, poly1.getConstant());
		} else if (poly2.isConstant()) {
			return mul(poly1, poly2.getConstant());
		} else {
			throw new UnsupportedOperationException("The outcome of this product is not affine!");
		}
	}

	/**
	 * Returns an AffineTerm which represents the quotient of the given arguments (see
	 * {@PolynomialTermTransformer #divide(Sort, IPolynomialTerm[])}).
	 */
	public static IPolynomialTerm divide(final IPolynomialTerm[] affineArgs, final Script script) {
		return constructDivision(affineArgs, "/", script);
	}
	
	/**
	 * Construct the division of the given polynomialTerms. If this is not possible, treat the whole
	 * division term as a variable and return it, wrapped in an AffineTerm. To distinguish, which
	 * division is used here, funcName is needed. This should be either "div" or "/".
	 */
	private static IPolynomialTerm constructDivision(final IPolynomialTerm[] affineArgs, 
													 final String funcName, 
													 final Script script) {
		final IPolynomialTerm affineTerm;
		Rational multiplier;
		if (affineArgs[0].isConstant()) {
			affineTerm = null;
			multiplier = affineArgs[0].getConstant();
		} else {
			affineTerm = affineArgs[0];
			multiplier = Rational.ONE;
		}
		final AffineTerm result;
		for (int i = 1; i < affineArgs.length; i++) {
			if (affineArgs[i].isConstant() && !affineArgs[i].isZero()) {
				multiplier = multiplier.mul(affineArgs[i].getConstant().inverse());
			} else {
				// Only the argument at position 0 may be a non-constant,
				// all other arguments must be literals,
				// divisors must not be zero.
				if (funcName == "div") {
					final Term term = PolynomialTermUtils.constructIteratedTerm("div", affineArgs, script);
					return constructVariable(term);
				}else if (funcName == "/") {
					final Term term = PolynomialTermUtils.constructIteratedTerm("/", affineArgs, script);
					return constructVariable(term);
				}else {
					throw new UnsupportedOperationException("FuncName does not match any known division.");
				}
			}
		}
		if (affineTerm == null) {
			result = AffineTerm.constructConstant(affineArgs[0].getSort(), multiplier);
		} else {
			result = AffineTerm.mul(affineTerm, multiplier);
		}
		return result;
	}
	
	

	/**
	 * Returns an AffineTerm which represents the integral quotient of the given arguments (see
	 * {@PolynomialTermTransformer #div(Sort, IPolynomialTerm[])}).
	 */
	public static IPolynomialTerm div(final IPolynomialTerm[] affineArgs, final Script script) {
		final IPolynomialTerm result = constructDivision(affineArgs, "div", script);
		if (result.isIntegral()) {
			return result;
		}
		final Term term = PolynomialTermUtils.constructIteratedTerm("div", affineArgs, script);
		return constructVariable(term);
	}

	/**
	 * @return unmodifiable map where each variable is mapped to its coefficient.
	 */
	public Map<Term, Rational> getVariable2Coefficient() {
		return Collections.unmodifiableMap(mAbstractVariable2Coefficient);
	}

	public static AffineTerm applyModuloToAllCoefficients(final Script script, final AffineTerm affineTerm,
			final BigInteger divident) {
		final GeneralizedConstructor<Term, AffineTerm> constructor = AffineTerm::new;
		return PolynomialTermUtils.applyModuloToAllCoefficients(affineTerm, divident, constructor);
	}

	@Override
	public Map<Monomial, Rational> getMonomial2Coefficient() {
		return mAbstractVariable2Coefficient.entrySet().stream()
				.collect(Collectors.toMap(x -> new Monomial(x.getKey(), Rational.ONE), Entry::getValue));
	}

	@Override
	public boolean isAffine() {
		return true;
	}

	/**
	 * @return true iff var is a variable of this {@link AffineTerm} (i.e., if this variable has a non-zero coefficient)
	 *         Note that for returning true it is especially NOT sufficient if var occurs only as a subterm of some
	 *         variable.
	 */
	@Override
	public boolean isVariable(final Term var) {
		return mAbstractVariable2Coefficient.containsKey(var);
	}

	@Override
	protected Term abstractVariableToTerm(final Script script, final Term abstractVariable) {
		return abstractVariable;
	}

}
