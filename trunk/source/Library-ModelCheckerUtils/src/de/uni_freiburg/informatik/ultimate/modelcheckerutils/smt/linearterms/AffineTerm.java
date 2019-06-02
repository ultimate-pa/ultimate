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
public class AffineTerm extends AbstractGeneralizedAffineTerm<Term> implements IPolynomialTerm {

	/**
	 * {@inheritDoc}
	 */
	public AffineTerm() {
		super();
	}

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


	/**
	 * Constructor to be used of all static methods that construct an affineTerm.
	 */
	AffineTerm(final Sort s, final Rational constant, final Map<Term, Rational> variables2coeffcient) {
		super(s, constant, variables2coeffcient);
	}

	/**
	 * {@inheritDoc}
	 */
	public AffineTerm(final Sort sort, final Term[] terms, final Rational[] coefficients, final Rational constant) {
		super(sort, terms, coefficients, constant);
	}

	/**
	 * @returns {@link AffineTerm} that has sort s and represents a Term of the
	 *          given {@link Rational} value.
	 */
	public static AffineTerm constructConstant(final Sort s, final Rational constant) {
		return new AffineTerm(s, constant, Collections.emptyMap());
	}

	/**
	 * {@link AffineTerm} that consists of the single variable that is represented by
	 * the {@link Term} t.
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











	/**
	 * @return unmodifiable map where each variable is mapped to its coefficient.
	 */
	public Map<Term, Rational> getVariable2Coefficient() {
		return Collections.unmodifiableMap(mVariable2Coefficient);
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
	public Map<Monomial, Rational> getMonomial2Coefficient() {
		return mVariable2Coefficient.entrySet().stream()
				.collect(Collectors.toMap(x -> new Monomial(x.getKey(), Rational.ONE), Entry::getValue));
	}

	@Override
	public boolean isAffine() {
		return true;
	}

	@Override
	protected Term abstractVariableToTerm(final Script script, final Term abstractVariable) {
		return abstractVariable;
	}

}
