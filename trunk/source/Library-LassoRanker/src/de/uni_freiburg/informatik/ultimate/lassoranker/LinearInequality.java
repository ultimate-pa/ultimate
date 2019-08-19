/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.io.Serializable;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermIsNotAffineException;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.UnknownFunctionException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * This represents an affine-linear inequality of the form
 *
 * <pre>
 * Σ c_i * x_i + c ⊳ 0
 * </pre>
 *
 * where c_i, c are affine terms possibly containing other variables, x_i are variables and ⊳ is > or ≥.
 *
 * The variables x_i used here are program variables, while the variables contained in the affine terms c_i, c are
 * parameters from the ranking function / supporting invariant templates. After the Motzkin transformation, the program
 * variables x_i will be eliminated while the parameters in c_i, c persist. This is why they are separated in this data
 * structure.
 *
 * @author Jan Leike
 */
public class LinearInequality implements Serializable {
	private static final long serialVersionUID = 5640678756293667730L;

	/**
	 * Possible values the Motzkin coefficient of this linear inequality can attain.
	 */
	public enum PossibleMotzkinCoefficients {
		ONE, ZERO_AND_ONE, ANYTHING;

		/**
		 * @return whether this attains more than one value
		 */
		public boolean multipleValues() {
			return this == ZERO_AND_ONE || this == ANYTHING;
		}

		/**
		 * @return whether this is fixed to a finite number of values
		 */
		public boolean isFixed() {
			return this == ONE || this == ZERO_AND_ONE;
		}
	}

	/**
	 * Whether the inequality is strict (">") versus non-strict ("≥")
	 */
	private boolean mStrict = false;

	/**
	 * What kind of Motzkin coefficients this inequality needs
	 */
	public PossibleMotzkinCoefficients mMotzkinCoefficient = PossibleMotzkinCoefficients.ANYTHING;

	/**
	 * List of variables and their coefficients
	 */
	private final Map<Term, AffineTerm> mCoefficients;

	/**
	 * Affine constant
	 */
	private AffineTerm mConstant;

	/**
	 * Construct an empty linear inequality, i.e. 0 ≥ 0.
	 */
	public LinearInequality() {
		mCoefficients = new LinkedHashMap<>();
		mConstant = new AffineTerm();
	}

	/**
	 * Copy constructor
	 */
	public LinearInequality(final LinearInequality other) {
		mConstant = new AffineTerm(other.mConstant);
		mStrict = other.mStrict;
		mMotzkinCoefficient = other.mMotzkinCoefficient;
		mCoefficients = new LinkedHashMap<>();
		for (final Map.Entry<Term, AffineTerm> entry : other.mCoefficients.entrySet()) {
			mCoefficients.put(entry.getKey(), new AffineTerm(entry.getValue()));
		}
	}

	public static LinearInequality constructFalse() {
		final LinearInequality result = new LinearInequality();
		result.setStrict(true);
		return result;
	}

	/**
	 * Construct an linear inequality from a Term instance.
	 *
	 * @param term
	 *            an affine-linear sum of values with termvariables
	 * @throws TermIsNotAffineException
	 *             if the term was not an affine-linear sum
	 */
	public static LinearInequality fromTerm(final Term term) throws TermException {
		LinearInequality li;
		if (term instanceof ConstantTerm) {
			li = new LinearInequality();
			li.add(new AffineTerm(SmtUtils.convertConstantTermToRational((ConstantTerm) term)));
		} else if (term instanceof TermVariable) {
			li = new LinearInequality();
			li.add(term, Rational.ONE);
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appt = (ApplicationTerm) term;
			if ("+".equals(appt.getFunction().getName())) {
				li = fromTerm(appt.getParameters()[0]);
				for (int i = 1; i < appt.getParameters().length; ++i) {
					li.add(fromTerm(appt.getParameters()[i]));
				}
			} else if ("-".equals(appt.getFunction().getName())) {
				if (appt.getFunction().getParameterSorts().length == 1) {
					// unary minus
					li = fromTerm(appt.getParameters()[0]);
					li.mult(Rational.MONE);
				} else { // binary minus (and polyary minus)
					li = fromTerm(appt.getParameters()[0]);
					li.mult(Rational.MONE);
					for (int i = 1; i < appt.getParameters().length; ++i) {
						li.add(fromTerm(appt.getParameters()[i]));
					}
					li.mult(Rational.MONE);
				}
			} else if ("*".equals(appt.getFunction().getName())) {
				li = new LinearInequality();
				li.mConstant = new AffineTerm(Rational.ONE);
				for (final Term u : appt.getParameters()) {
					final LinearInequality liu = fromTerm(u);
					if (li.isConstant() && li.mConstant.isConstant()) {
						liu.mult(li.mConstant.getConstant());
						li = liu;
					} else if (liu.isConstant() && liu.mConstant.isConstant()) {
						li.mult(liu.mConstant.getConstant());
					} else {
						throw new TermIsNotAffineException(TermIsNotAffineException.s_MultipleNonConstantFactors, appt);
					}
				}
			} else if ("/".equals(appt.getFunction().getName())) {
				assert appt.getParameters().length == 2;
				final LinearInequality divident = fromTerm(appt.getParameters()[0]);
				final LinearInequality divisor = fromTerm(appt.getParameters()[1]);
				if (!divisor.isConstant() || !divisor.mConstant.isConstant()) {
					throw new TermIsNotAffineException(TermIsNotAffineException.s_NonConstantDivisor, appt);
				} else if (divisor.mConstant.getConstant().equals(Rational.ZERO)) {
					throw new TermIsNotAffineException(TermIsNotAffineException.s_DivisionByZero, appt);
				} else {
					li = divident;
					li.mult(divisor.mConstant.getConstant().inverse());
				}
			} else if (appt.getParameters().length == 0) {
				li = new LinearInequality();
				li.add(appt, Rational.ONE);
			} else {
				throw new UnknownFunctionException(appt);
			}
		} else {
			throw new TermException(TermException.UNKNOWN_SUBCLASS_OF_TERM, term);
		}
		return li;
	}

	/**
	 * @return true iff the affine term is just a constant
	 */
	public boolean isConstant() {
		return mCoefficients.isEmpty() && mConstant.isConstant();
	}

	/**
	 * @return whether all coefficients are constants
	 */
	public boolean allAffineTermsAreConstant() {
		boolean result = true;
		result &= mConstant.isConstant();
		for (final AffineTerm coeff : mCoefficients.values()) {
			result &= coeff.isConstant();
		}
		return result;
	}

	/**
	 * @return the constant component
	 */
	public AffineTerm getConstant() {
		return mConstant;
	}

	/**
	 * Is this a strict inequality?
	 */
	public boolean isStrict() {
		return mStrict;
	}

	/**
	 * Set whether this is a strict inequality
	 */
	public void setStrict(final boolean strict) {
		mStrict = strict;
	}

	/**
	 * Returns '>' if this is a strict inequality and '>=' otherwise
	 */
	public String getInequalitySymbol() {
		return mStrict ? ">" : ">=";
	}

	/**
	 * Returns '<' if this is a strict inequality and '<=' otherwise
	 */
	public String getInequalitySymbolReverse() {
		return mStrict ? "<" : "<=";
	}

	/**
	 * Return a variable's coefficient
	 *
	 * @param var
	 *            a variable
	 * @return zero if the variable does not occur
	 */
	public AffineTerm getCoefficient(final Term var) {
		final AffineTerm p = mCoefficients.get(var);
		if (p == null) {
			return new AffineTerm();
		}
		return p;
	}

	/**
	 * @return a collection of all occuring variables
	 */
	public Collection<Term> getVariables() {
		return mCoefficients.keySet();
	}

	/**
	 * Add another linear inequality
	 *
	 * @param li
	 *            other linear inequality
	 */
	public void add(final LinearInequality li) {
		this.add(li.mConstant);
		for (final Map.Entry<Term, AffineTerm> entry : li.mCoefficients.entrySet()) {
			this.add(entry.getKey(), entry.getValue());
		}
	}

	/**
	 * Add another coefficients to the linear inequality
	 *
	 * @param var
	 *            variable
	 * @param t
	 *            the variable's coefficient to be added
	 */
	public void add(final Term var, final AffineTerm a) {
		final AffineTerm a2 = mCoefficients.get(var);
		if (a2 != null) {
			a2.add(a);
			if (!a2.isZero()) {
				mCoefficients.put(var, a2);
			} else {
				mCoefficients.remove(var);
			}
		} else {
			if (!a.isZero()) {
				mCoefficients.put(var, a);
			}
		}
	}

	/**
	 * Add another coefficients to the linear inequality
	 *
	 * @param var
	 *            variable
	 * @param t
	 *            the variable's coefficient to be added
	 */
	public void add(final Term var, final Rational r) {
		this.add(var, new AffineTerm(r));
	}

	/**
	 * Add a constant to the linear inequality
	 *
	 * @param t
	 *            a constant
	 */
	public void add(final AffineTerm p) {
		mConstant.add(p);
	}

	/**
	 * Multiply with a constant
	 *
	 * @param t
	 *            factor
	 */
	public void mult(final Rational r) {
		mConstant.mult(r);
		for (final Map.Entry<Term, AffineTerm> entry : mCoefficients.entrySet()) {
			entry.getValue().mult(r);
		}
	}

	/**
	 * Negate the linear inequality
	 *
	 * <pre>
	 * a > b --> b ≥ a (resp. t > 0 ~~> -t ≥ 0)
	 * for reals
	 *     a ≥ b --> b > a (resp. t ≥ 0 ~~> -t > 0)
	 * for ints
	 *     a ≥ b --> b ≥ a + 1 (resp. t ≥ 0 ~~> -t-1 ≥ 0)
	 * </pre>
	 * 
	 */
	public void negate() {
		mult(Rational.MONE);
		if (false && !mStrict && getSortName().equals("Int")) {
			add(new AffineTerm(BigInteger.valueOf(-1)));
		} else {
			mStrict = !mStrict;
		}
	}

	/**
	 * @return the name of the Sort of the summands ("Real" or "Int")
	 */
	public String getSortName() {
		if (mCoefficients.isEmpty()) {
			// default to Real
			return SmtSortUtils.REAL_SORT;
		}
		final Term firstVar = mCoefficients.keySet().iterator().next();
		final Sort result = firstVar.getSort();
		for (final Term var : mCoefficients.keySet()) {
			assert var.getSort() == result;
		}
		return result.getName();
	}

	/**
	 * @param script
	 *            current SMT script
	 * @return this as a term
	 */
	public Term asTerm(final Script script) {
		final String sortName = getSortName();
		final boolean real = sortName.equals(SmtSortUtils.REAL_SORT);
		final Term[] summands = new Term[mCoefficients.size() + 1];
		final Term zero = real ? script.decimal(BigDecimal.ZERO) : SmtUtils.constructIntValue(script, BigInteger.ZERO);

		int i = 0;
		for (final Entry<Term, AffineTerm> entry : mCoefficients.entrySet()) {
			final Term var = entry.getKey();
			Term coeff;
			if (real) {
				assert SmtSortUtils.isRealSort(var.getSort());
				coeff = entry.getValue().asRealTerm(script);
			} else {
				assert SmtSortUtils.isIntSort(var.getSort());
				coeff = entry.getValue().asIntTerm(script);
			}
			summands[i] = script.term("*", coeff, entry.getKey());
			++i;
		}

		if (real) {
			summands[i] = mConstant.asRealTerm(script);
		} else {
			summands[i] = mConstant.asIntTerm(script);
		}
		final Term sum = SmtUtils.sum(script, script.sort(sortName), summands);

		return script.term(getInequalitySymbol(), sum, zero);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("0 ");
		sb.append(getInequalitySymbolReverse());
		sb.append(" ");
		boolean first = true;
		for (final Map.Entry<Term, AffineTerm> entry : mCoefficients.entrySet()) {
			if (entry.getValue().isZero()) {
				continue;
			}
			final String param = entry.getValue().toString();
			if (param.length() > 2 && param.substring(2).contains(" ")) {
				if (!first) {
					sb.append(" + ");
				}
				sb.append("(");
				sb.append(param);
				sb.append(")");
			} else if (param.startsWith("-")) {
				if (!first) {
					sb.append(" -");
					sb.append(param.substring(1));
				} else {
					sb.append(param);
				}
			} else {
				if (!first) {
					sb.append(" + ");
				}
				sb.append(param);
			}
			sb.append("*");
			sb.append(entry.getKey());
			first = false;
		}
		if (!mConstant.isZero() || first) {
			final String s = mConstant.toString();
			if (s.startsWith("-")) {
				if (!first) {
					sb.append(" -");
					sb.append(s.substring(1));
				} else {
					sb.append(s);
				}
			} else {
				if (!first) {
					sb.append(" + ");
				}
				sb.append(s);
			}
		}
		return sb.toString();
	}
}
