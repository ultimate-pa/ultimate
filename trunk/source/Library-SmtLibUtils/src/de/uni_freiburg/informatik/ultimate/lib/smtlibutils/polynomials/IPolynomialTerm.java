/*
 * Copyright (C) 2019 Leonard Fichtner
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

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AbstractGeneralizedAffineTerm.Equivalence;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * This represents a term in form of
 *
 * <pre>
* Σ c_i * x_i^{e_i} + c
 * </pre>
 *
 * where c_i, c, e_i are literals, and x_i are variables.
 *
 * @author Leonard Fichtner (leonard.fichtner@web.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public interface IPolynomialTerm {

	/**
	 * True if this represents not an polynomial or affine term but an error during the translation process, e.g., if
	 * original term had wrong sorts.
	 */
	boolean isErrorTerm();

	/**
	 * Transforms this PolynomialTerm into a Term that is supported by the solver.
	 *
	 * @param script
	 *            Script for that this term is constructed.
	 */
	Term toTerm(Script script);

	/**
	 * @return unmodifiable map where each variable (wrapped as Monomial) is mapped to its coefficient.
	 */
	Map<Monomial, Rational> getMonomial2Coefficient();

	/**
	 * @return whether this polynomial term is just a constant
	 */
	boolean isConstant();

	/**
	 * @return true iff this term is affine linear (i.e., each monomial consists only of a single variable)
	 */
	boolean isAffine();

	/**
	 * @return whether this polynomial term is zero
	 */
	boolean isZero();

	/**
	 * @return whether this polynomial has integral coefficients and constant.
	 */
	boolean isIntegral();

	/**
	 * @return the constant summand of this polynomial term
	 */
	Rational getConstant();

	Sort getSort();

	/**
	 * @return A new {@link IPolynomialTerm} that is the multiplication of this
	 *         {@link IPolynomialTerm} with a {@link Rational literal}
	 */
	default IPolynomialTerm mul(final Rational rat) {
		// TODO 20220730 Matthias: Do refactor that implements more methods in
		// subclasses (instead of static methods).
		if (this instanceof AffineTerm) {
			return AffineTerm.mul(this, rat);
		} else if (this instanceof PolynomialTerm) {
			return PolynomialTerm.mul(this, rat);
		} else {
			throw new UnsupportedOperationException("Unsupported kind of polynomial");
		}
	}


	/**
	 * @return Divide this {@link IPolynomialTerm} by divisor. Return the result
	 *         only if there is some "inverse" element invrs such that a
	 *         multiplication with invrs is equivalent to the original
	 *         {@link IPolynomialTerm}. Return null if no such inverse element
	 *         exists.
	 */
	IPolynomialTerm divInvertible(Rational divisor);

	/**
	 * @return
	 *         <ul>
	 *         <li>{@link Equivalence#EQUALS} if (= this otherTerm) is valid for all
	 *         variable assignments
	 *         <li>{@link Equivalence#DISTINCT} if (not (= this otherTerm)) is valid
	 *         for all variable assignments
	 *         <li>{@link Equivalence#INCOMPARABLE} otherwise. </ ul>
	 *
	 */
	Equivalence compare(IPolynomialTerm otherTerm);

	/**
	 * @return A new {@link IPolynomialTerm} that is differs from this only in an
	 *         offset that was added.
	 */
	IPolynomialTerm add(final Rational offset);

	/**
	 * Compute the GCD of all coefficients (but do not include the constant in the
	 * computation). E.g., this method returns 2 for the polynomial 4*x+6*y+5. We
	 * use the semantics of {@link Rational#gcd}. If there are no coefficients, we
	 * return the {@link Rational} zero.
	 */
	Rational computeGcdOfCoefficients();

	IPolynomialTerm div(final Script script, final IPolynomialTerm... divisors);

	IPolynomialTerm mod(final Script script, final IPolynomialTerm divisor);

}