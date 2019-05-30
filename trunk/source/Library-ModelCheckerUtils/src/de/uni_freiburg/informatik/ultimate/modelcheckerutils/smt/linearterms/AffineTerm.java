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
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.PolynomialTermUtils.GeneralizedConstructor;

/**
 * This represents an affine term in the form of
 *
 * <pre>
 * Σ c_i * x_i + c,
 * </pre>
 *
 * where c_i, c are literals and x_i are variables. We consider every term as a
 * variable unless is is an {@link ApplicationTerm} whose {@link FunctionSymbol}
 * is an "affine symbol" {@link AffineTermTransformer#isAffineSymbol}. Hence
 * variables are e.g., {@link TermVariable}, constants (i.e., 0-ary function
 * symbols), function applications, array read expressions (i.e., select terms)
 * <p>
 * Note that this class extends {@link Term} but it is not supported by the
 * solver. We extend Term only that this can be returned by a TermTransformer.
 * </p>
 * <p>
 * Note that there is a class (@link
 * de.uni_freiburg.informatik.ultimate.smtinterpol.convert.AffineTerm} which is
 * somehow similar but we cannot extend it because it too closely interweaved
 * with the SMTInterpol.
 * </p>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Jan Leike
 */
public class AffineTerm extends Term implements IPolynomialTerm {
	/**
	 * Map from Variables to coeffcients. Coefficient Zero is forbidden.
	 */
	private final Map<Term, Rational> mVariable2Coefficient;

	/**
	 * Affine constant (the coefficient without variable).
	 */
	private final Rational mConstant;

	/**
	 * Sort of this term. E.g, "Int" or "Real".
	 */
	private final Sort mSort;


	/*======================== This is new ===================*/

	/**
	 * Calculate the map of the product of affineTerms (in Variable2Coefficient form).
	 */
	private static Map<Term, Rational> calculateProductMapOfAffineTerms(final IPolynomialTerm poly1, final IPolynomialTerm poly2){
		final Map<Term, Rational> map = new HashMap<>();
		if (poly1.isConstant()) {
			if (poly1.getConstant().equals(Rational.ZERO)) {
				return Collections.emptyMap();
			}
			for (final Map.Entry<Term, Rational> summand : ((AffineTerm) poly2).getVariable2Coefficient().entrySet()) {
				map.put(summand.getKey(), summand.getValue().mul(poly1.getConstant()));
			}
		//poly2 must be a constant then, or else the product will not be affine -> Error
		}else if (poly2.isConstant()){
			if (poly2.getConstant().equals(Rational.ZERO)) {
				return Collections.emptyMap();
			}
			for (final Map.Entry<Term, Rational> summand : ((AffineTerm) poly1).getVariable2Coefficient().entrySet()) {
				map.put(summand.getKey(), summand.getValue().mul(poly2.getConstant()));
			}
		}else {
			throw new UnsupportedOperationException("The outcome of this product is not affine!");
		}
		return shrinkMap(map);
	}

	/**
	 * Returns a shrinked version of a map if possible. Returns the given map otherwise.
	 */
	private static Map<Term, Rational> shrinkMap(final Map<Term, Rational> map){
		if (map.size() == 0) {
			return Collections.emptyMap();
		}
		else if (map.size() == 1) {
			final Entry<Term, Rational> entry = map.entrySet().iterator().next();
			return Collections.singletonMap(entry.getKey(), entry.getValue());
		}
		return map;
	}

	/**
	 * Calculate the constant of a sum of given IPolynomialTerms.
	 */
	private static Rational calculateSumConstant(final IPolynomialTerm...polynomialTerms) {
		Rational constant = Rational.ZERO;
		final Sort s = polynomialTerms[0].getSort();
		for (final IPolynomialTerm polynomialTerm : polynomialTerms) {
			if (SmtSortUtils.isBitvecSort(s)) {
				constant = PolynomialTermUtils.bringValueInRange(constant.add(polynomialTerm.getConstant()), s);
			} else {
				constant = constant.add(polynomialTerm.getConstant());
			}
		}
		return constant;
	}

	private static Map<Term, Rational> calculateSumMapOfAffineTerms(final IPolynomialTerm... affineTerms){
		final Sort s = affineTerms[0].getSort();
		final Map<Term, Rational> map = new HashMap<>();
		for (final IPolynomialTerm affineTerm : affineTerms) {
			for (final Map.Entry<Term, Rational> summand : ((AffineTerm) affineTerm).getVariable2Coefficient().entrySet()) {
				assert summand.getKey().getSort() == s : "Sort mismatch: " + summand.getKey().getSort() + " vs. "
						+ s;
				final Rational coeff = map.get(summand.getKey());
				if (coeff == null) {
					map.put(summand.getKey(), summand.getValue());
				} else {
					final Rational newCoeff;
					if (SmtSortUtils.isBitvecSort(s)) {
						newCoeff = PolynomialTermUtils.bringValueInRange(coeff.add(summand.getValue()), s);
					} else {
						newCoeff = coeff.add(summand.getValue());
					}
					if (newCoeff.equals(Rational.ZERO)) {
						map.remove(summand.getKey());
					} else {
						map.put(summand.getKey(), newCoeff);
					}
				}
			}
		}
		return shrinkMap(map);
	}

	/*======================= Until here ==================*/

	static AffineTerm sum(final IPolynomialTerm... summands) {
		final GeneralizedConstructor<Term, AffineTerm> constructor = AffineTerm::construct;
		return PolynomialTermUtils.constructSum(x -> ((AffineTerm) x).getVariable2Coefficient(), constructor, summands);
	}

	static AffineTerm construct(final Sort sort, final Rational constant, final Map<Term, Rational> variables2coeffcient) {
		return new AffineTerm(sort, constant, variables2coeffcient);
	}

	/**
	 * Constructor to be used of all static methods that construct an affineTerm.
	 */
	private AffineTerm(final Sort s, final Rational constant, final Map<Term, Rational> variables2coeffcient) {
		super(0);
		mSort = s;
		mConstant = constant;
		mVariable2Coefficient = variables2coeffcient;
	}


	/**
	 * AffineTerm that represents the Rational r of sort s.
	 */
	public AffineTerm(final Sort s, final Rational r) {
		super(0);
		mSort = s;
		mConstant = r;
		mVariable2Coefficient = Collections.emptyMap();
	}

	/**
	 * {@linkAffineTerm} that consists of the single variable that is represented by
	 * the {@link Term} t.
	 */
	public AffineTerm(final Term t) {
		super(0);
		mSort = t.getSort();
		mConstant = Rational.ZERO;
		mVariable2Coefficient = Collections.singletonMap(t, Rational.ONE);
	}

	/**
	 * AffineTerm whose variables are given by an array of terms, whose corresponding coefficients are given by the
	 * array coefficients, and whose constant term is given by the Rational constant.
	 */
	public AffineTerm(final Sort s, final Term[] terms, final Rational[] coefficients, final Rational constant) {
		super(0);
		mSort = s;
		mConstant = constant;
		if (terms.length != coefficients.length) {
			throw new IllegalArgumentException("number of variables and coefficients different");
		}
		switch (terms.length) {
		case 0:
			mVariable2Coefficient = Collections.emptyMap();
			break;
		case 1:
			final Term variable = terms[0];
			checkIfTermIsLegalVariable(variable);
			if (coefficients[0].equals(Rational.ZERO)) {
				mVariable2Coefficient = Collections.emptyMap();
			} else {
				mVariable2Coefficient = Collections.singletonMap(variable, coefficients[0]);
			}
			break;
		default:
			mVariable2Coefficient = new HashMap<>();
			for (int i = 0; i < terms.length; i++) {
				checkIfTermIsLegalVariable(terms[i]);
				if (!coefficients[i].equals(Rational.ZERO)) {
					mVariable2Coefficient.put(terms[i], coefficients[i]);
				}
			}
			break;
		}
	}

	/**
	 * Check if term is of a type that may be a variable of an AffineTerm.
	 */
	public void checkIfTermIsLegalVariable(final Term term) {
		if (term instanceof TermVariable || term instanceof ApplicationTerm) {
			// term is ok
		} else {
			throw new IllegalArgumentException("Variable of AffineTerm has to be TermVariable or ApplicationTerm");
		}
	}

	/**
	 * AffineTerm that represents the sum of affineTerms.
	 */
	public AffineTerm(final AffineTerm... affineTerms) {
		super(0);
		mSort = affineTerms[0].getSort();
		mVariable2Coefficient = new HashMap<>();
		Rational constant = Rational.ZERO;
		for (final AffineTerm affineTerm : affineTerms) {
			for (final Map.Entry<Term, Rational> summand : affineTerm.mVariable2Coefficient.entrySet()) {
				assert summand.getKey().getSort() == mSort : "Sort mismatch: " + summand.getKey().getSort() + " vs. "
						+ mSort;
				final Rational coeff = mVariable2Coefficient.get(summand.getKey());
				if (coeff == null) {
					mVariable2Coefficient.put(summand.getKey(), summand.getValue());
				} else {
					final Rational newCoeff;
					if (SmtSortUtils.isBitvecSort(mSort)) {
						newCoeff = PolynomialTermUtils.bringValueInRange(coeff.add(summand.getValue()), mSort);
					} else {
						newCoeff = coeff.add(summand.getValue());
					}
					if (newCoeff.equals(Rational.ZERO)) {
						mVariable2Coefficient.remove(summand.getKey());
					} else {
						mVariable2Coefficient.put(summand.getKey(), newCoeff);
					}
				}
			}
			if (SmtSortUtils.isBitvecSort(mSort)) {
				constant = PolynomialTermUtils.bringValueInRange(constant.add(affineTerm.mConstant), mSort);
			} else {
				constant = constant.add(affineTerm.mConstant);
			}
		}
		mConstant = constant;
	}

	/**
	 * AffineTerm that represents the product of affineTerm and multiplier.
	 */
	public AffineTerm(final AffineTerm affineTerm, final Rational multiplier) {
		super(0);
		if (multiplier.equals(Rational.ZERO)) {
			mSort = affineTerm.getSort();
			mConstant = Rational.ZERO;
			mVariable2Coefficient = Collections.emptyMap();
		} else {
			mVariable2Coefficient = new HashMap<>();
			mSort = affineTerm.getSort();
			if (SmtSortUtils.isBitvecSort(mSort)) {
				mConstant = PolynomialTermUtils.bringValueInRange(affineTerm.mConstant.mul(multiplier), mSort);
			} else {
				assert mSort.isNumericSort();
				mConstant = affineTerm.mConstant.mul(multiplier);
			}
			for (final Map.Entry<Term, Rational> summand : affineTerm.mVariable2Coefficient.entrySet()) {
				mVariable2Coefficient.put(summand.getKey(), summand.getValue().mul(multiplier));
			}
		}
	}



	/**
	 * Auxiliary affine term that represents an error during the translation process, e.g., if original term was not
	 * linear.
	 */
	public AffineTerm() {
		super(0);
		mVariable2Coefficient = null;
		mConstant = null;
		mSort = null;
	}

	/**
	 * True if this represents not an affine term but an error during the translation process, e.g., if original term
	 * was not linear.
	 */
	@Override
	public boolean isErrorTerm() {
		if (mVariable2Coefficient == null) {
			assert mConstant == null;
			assert mSort == null;
			return true;
		} else {
			assert mConstant != null;
			assert mSort != null;
			return false;
		}
	}

	/**
	 * @return whether this affine term is just a constant
	 */
	@Override
	public boolean isConstant() {
		return mVariable2Coefficient.isEmpty();
	}

	/**
	 * @return whether this affine term is zero
	 */
	@Override
	public boolean isZero() {
		return mConstant.equals(Rational.ZERO) && mVariable2Coefficient.isEmpty();
	}

	/**
	 * @return the constant summand of this affine term
	 */
	@Override
	public Rational getConstant() {
		return mConstant;
	}

	/**
	 * @return unmodifiable map where each variable is mapped to its coefficient.
	 */
	public Map<Term, Rational> getVariable2Coefficient() {
		return Collections.unmodifiableMap(mVariable2Coefficient);
	}

	/**
	 * Transforms this AffineTerm into a Term that is supported by the solver.
	 *
	 * @param script
	 *            Script for that this term is constructed.
	 */
	@Override
	public Term toTerm(final Script script) {
		Term[] summands;
		if (mConstant.equals(Rational.ZERO)) {
			summands = new Term[mVariable2Coefficient.size()];
		} else {
			summands = new Term[mVariable2Coefficient.size() + 1];
		}
		int i = 0;
		for (final Map.Entry<Term, Rational> entry : mVariable2Coefficient.entrySet()) {
			assert !entry.getValue().equals(Rational.ZERO) : "zero is no legal coefficient in AffineTerm";
			if (entry.getValue().equals(Rational.ONE)) {
				summands[i] = entry.getKey();
			} else {
				final Term coeff = SmtUtils.rational2Term(script, entry.getValue(), mSort);
				summands[i] = SmtUtils.mul(script, mSort, coeff, entry.getKey());
			}
			++i;
		}
		if (!mConstant.equals(Rational.ZERO)) {
			assert mConstant.isIntegral() || SmtSortUtils.isRealSort(mSort);
			summands[i] = SmtUtils.rational2Term(script, mConstant, mSort);
		}
		final Term result = SmtUtils.sum(script, mSort, summands);
		return result;
	}

	/**
	 * Transforms this AffineTerm into an equivalent PolynomialTerm.
	 */
	@Deprecated
	public IPolynomialTerm toPolynomialTerm() {
		final int arraylength = mVariable2Coefficient.entrySet().size();
		final Rational[] coefficients = new Rational[arraylength];
		final Term[] terms = new Term[arraylength];
		int index = 0;
		for (final Map.Entry<Term, Rational> entry : mVariable2Coefficient.entrySet()) {
			terms[index] = entry.getKey();
			coefficients[index] = entry.getValue();
			index++;
		}
		return new PolynomialTerm(mSort, terms, coefficients, mConstant);
	}

	@Override
	public String toString() {
		if (isErrorTerm()) {
			return "auxilliaryErrorTerm";
		}
		final StringBuilder sb = new StringBuilder();
		for (final Map.Entry<Term, Rational> entry : mVariable2Coefficient.entrySet()) {
			sb.append(entry.getValue().isNegative() ? " - " : " + ");
			sb.append(entry.getValue().abs() + "*" + entry.getKey());
		}
		if (!mConstant.equals(Rational.ZERO) || sb.length() == 0) {
			if (mConstant.isNegative() || sb.length() > 0) {
				sb.append(mConstant.isNegative() ? " - " : " + ");
			}
			sb.append(mConstant.abs());
		}
		String result = sb.toString();
		if (result.charAt(0) == ' ') {
			result = result.substring(1); // Drop first space
		}

		return result;
	}

	@Override
	public Sort getSort() {
		return mSort;
	}

	@Override
	public void toStringHelper(final ArrayDeque<Object> mTodo) {
		throw new UnsupportedOperationException("This is an auxilliary Term and not supported by the solver");
	}

	public static AffineTerm applyModuloToAllCoefficients(final Script script, final AffineTerm affineTerm,
			final BigInteger divident) {
		assert SmtSortUtils.isIntSort(affineTerm.getSort());
		final Map<Term, Rational> map = affineTerm.getVariable2Coefficient();
		final Term[] terms = new Term[map.size()];
		final Rational[] coefficients = new Rational[map.size()];
		int offset = 0;
		for (final Entry<Term, Rational> entry : map.entrySet()) {
			terms[offset] = entry.getKey();
			coefficients[offset] =
					SmtUtils.toRational(BoogieUtils.euclideanMod(SmtUtils.toInt(entry.getValue()), divident));
			offset++;
		}
		final Rational constant =
				SmtUtils.toRational(BoogieUtils.euclideanMod(SmtUtils.toInt(affineTerm.getConstant()), divident));
		return new AffineTerm(affineTerm.getSort(), terms, coefficients, constant);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (mConstant == null ? 0 : mConstant.hashCode());
		result = prime * result + (mSort == null ? 0 : mSort.hashCode());
		result = prime * result + (mVariable2Coefficient == null ? 0 : mVariable2Coefficient.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (!(obj instanceof AffineTerm)) {
			return false;
		}
		final AffineTerm other = (AffineTerm) obj;
		if (mConstant == null) {
			if (other.mConstant != null) {
				return false;
			}
		} else if (!mConstant.equals(other.mConstant)) {
			return false;
		}
		if (mSort == null) {
			if (other.mSort != null) {
				return false;
			}
		} else if (!mSort.equals(other.mSort)) {
			return false;
		}
		if (mVariable2Coefficient == null) {
			if (other.mVariable2Coefficient != null) {
				return false;
			}
		} else if (!mVariable2Coefficient.equals(other.mVariable2Coefficient)) {
			return false;
		}
		return true;
	}

	@Override
	public Map<Monomial, Rational> getMonomial2Coefficient() {
		return mVariable2Coefficient.entrySet().stream()
				.collect(Collectors.toMap(x -> new Monomial(x.getKey(), Rational.ONE), Entry::getValue));
	}

	@Override
	public boolean isAffine() {
		return true;
	}

}
