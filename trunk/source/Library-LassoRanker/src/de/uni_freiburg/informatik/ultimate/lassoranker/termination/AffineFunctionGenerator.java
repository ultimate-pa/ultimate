/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2012-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lassoranker.termination;

import java.io.Serializable;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * The AffineFunctionGenerator creates template instances of affine-linear functions to be used in LinearInequality
 * instances.
 *
 * A valuation on the generated variables can be used to create an AffineFunction instance.
 *
 * @author Jan Leike
 */
public class AffineFunctionGenerator implements Serializable {
	private static final long serialVersionUID = 4376363192635730213L;

	private final Term mConstant;
	private final Map<IProgramVar, Term> mCoefficients;

	/**
	 * Name of the variable for the affine function's affine constant
	 */
	private static String constName(final String prefix) {
		return prefix + "c";
	}

	/**
	 * Name of the variable for the affine function's coefficients
	 */
	private static String coeffName(final String prefix, final IProgramVar var) {
		return prefix + "_" + SmtUtils.removeSmtQuoteCharacters(var.getGloballyUniqueId());
	}

	private AffineFunctionGenerator(final Term constant, final Map<IProgramVar, Term> coefficients) {
		mConstant = constant;
		mCoefficients = coefficients;
	}

	/**
	 * @param script
	 *            current SMT script
	 * @param variables
	 *            the set of variables that need coefficients
	 * @param prefix
	 *            new variables' name prefix
	 */
	public AffineFunctionGenerator(final Script script, final Collection<IProgramVar> variables, final String prefix) {
		// Create variables
		mConstant = SmtUtils.buildNewConstant(script, constName(prefix), SmtSortUtils.REAL_SORT);
		mCoefficients = new LinkedHashMap<>();
		for (final IProgramVar var : variables) {
			mCoefficients.put(var, SmtUtils.buildNewConstant(script, coeffName(prefix, var), SmtSortUtils.REAL_SORT));
		}
	}

	/**
	 * Constructors that creates an AffineFunctionGenerator with constant coefficients.
	 *
	 * @author Betim Musa <musab@informatik.uni-freiburg.de>
	 * @param script
	 * @param variables
	 * @param prefix
	 * @param withoutCoefficients
	 *            - is true, otherwise the call of this constructor doesn't make sense
	 */
	public AffineFunctionGenerator(final Script script, final Collection<IProgramVar> variables, final String prefix,
			final boolean withoutCoefficients) {
		assert withoutCoefficients : "This constructor is called only if the program variables shouldn't have any coefficients which"
				+ "need to be determined";
		// Create variables
		mConstant = SmtUtils.buildNewConstant(script, constName(prefix), SmtSortUtils.REAL_SORT);
		mCoefficients = new LinkedHashMap<>();
		// initialize all the coefficients with the numerical constant '1'
		for (final IProgramVar var : variables) {
			mCoefficients.put(var, SmtUtils.constructIntValue(script, BigInteger.ONE));
		}
	}

	/**
	 * Generate the linear inequality
	 *
	 * @param vars
	 *            a mapping from Boogie variables to TermVariables to be used
	 * @return Linear inequality corresponding to si(x)
	 */
	public LinearInequality generate(final Map<IProgramVar, ? extends Term> vars) {
		final LinearInequality li = new LinearInequality();
		li.add(new AffineTerm(mConstant, Rational.ONE));
		for (final Map.Entry<IProgramVar, ? extends Term> entry : vars.entrySet()) {
			if (mCoefficients.containsKey(entry.getKey())) {
				li.add(entry.getValue(), new AffineTerm(mCoefficients.get(entry.getKey()), Rational.ONE));
			}
		}
		return li;
	}

	/**
	 * Generates a linear inequality that has no free coefficients which need to be determined, all of its coefficients
	 * are constants.
	 *
	 * @author Betim Musa <musab@informatik.uni-freiburg.de>
	 * @param vars
	 *            a mapping from Boogie variables to TermVariables to be used
	 * @param programVars2NumericalCoefficients
	 *            a mapping from Boogie variables to their constant (numerical) coefficients
	 * @return Linear inequality corresponding to si(x)
	 */
	public LinearInequality generate(final Map<IProgramVar, ? extends Term> vars,
			final Map<IProgramVar, AffineTerm> programVars2NumericalCoefficients,
			final Map<Term, AffineTerm> auxVarsToNumericalCoefficients) {
		final LinearInequality li = new LinearInequality();
		for (final Map.Entry<IProgramVar, ? extends Term> entry : vars.entrySet()) {
			li.add(entry.getValue(), programVars2NumericalCoefficients.get(entry.getKey()));
		}
		for (final Map.Entry<Term, AffineTerm> entry : auxVarsToNumericalCoefficients.entrySet()) {
			li.add(entry.getKey(), entry.getValue());
		}
		return li;
	}

	/**
	 * Gets the coefficient for a given program variable.
	 *
	 * @param var
	 *            a IProgramVar
	 * @return the coefficient for the given program variable
	 */
	public Term getCoefficient(final IProgramVar var) {
		return mCoefficients.get(var);
	}

	/**
	 * @return All coefficients (including the constant) of the affine function. Each coefficient is represented as an
	 *         SMT variable.
	 */
	public Collection<Term> getCoefficients() {
		final Collection<Term> vars = new ArrayList<>(mCoefficients.values());
		vars.add(mConstant);
		return vars;
	}

	/**
	 * Extract the greatest common denominator of all coefficients and the constant of this affine function.
	 *
	 * @param assignment
	 *            the assignment to the function's coefficients
	 * @return the greatest common denominator
	 */
	public Rational getGcd(final Map<Term, Rational> assignment) {
		Rational gcd = assignment.get(mConstant);
		for (final Map.Entry<IProgramVar, Term> entry : mCoefficients.entrySet()) {
			gcd = gcd.gcd(assignment.get(entry.getValue()));
		}
		// use the absolute value of the GCD obtained from Rational.gcd
		// TODO: check with Jochen and Jürgen if negative GCD is a bug
		return gcd.abs();
	}

	/**
	 * Extract coefficients from the model and convert them to an AffineFunction
	 *
	 * The affine function's coefficients must be integers, so we have to divide them by their greatest common
	 * denominator. This method automatically determines the gcd for the function's coefficients.
	 *
	 * @param assignment
	 *            the assignment to the function's coefficients
	 * @return an instance of the affine function generated by this generator
	 */
	public AffineFunction extractAffineFunction(final Map<Term, Rational> assignment) {
		return extractAffineFunction(assignment, getGcd(assignment));
	}

	/**
	 * Extract coefficients from an assignment and convert them to an AffineFunction
	 *
	 * The affine function's coefficients must be integers, so we have to divide them by their greatest common
	 * denominator.
	 *
	 * @param assignment
	 *            the assignment to the function's coefficients
	 * @param gcd
	 *            a divisor for all values extracted from the assignment
	 * @return an instance of AffineFunction generated by this generator
	 */
	public AffineFunction extractAffineFunction(final Map<Term, Rational> assignment, final Rational gcd) {
		final AffineFunction f = new AffineFunction();
		if (gcd.equals(Rational.ZERO)) {
			// special case: gcd is zero, this happens only if all
			// coefficients are zero.
			Rational c = assignment.get(mConstant);
			assert (c.equals(Rational.ZERO));
			for (final Map.Entry<IProgramVar, Term> entry : mCoefficients.entrySet()) {
				c = assignment.get(entry.getValue());
				assert (c.equals(Rational.ZERO));
				f.put(entry.getKey(), c.numerator());
			}
		} else {
			// Divide all coefficients by the gcd
			Rational c = assignment.get(mConstant).div(gcd);
			assert (c.denominator().equals(BigInteger.ONE));
			f.setConstant(c.numerator());
			for (final Map.Entry<IProgramVar, Term> entry : mCoefficients.entrySet()) {
				c = assignment.get(entry.getValue()).div(gcd);
				assert (c.denominator().equals(BigInteger.ONE));
				f.put(entry.getKey(), c.numerator());
			}
		}
		return f;
	}

	/**
	 * Creates a AffineFunctionGenerator that produces a LinearInequality where all coefficients are negated.
	 *
	 * @param script
	 *            a script to transform terms
	 * @return a new AffineFunctionGenerator instance
	 */
	public AffineFunctionGenerator getGeneratorWithNegatedCoefficients(final Script script) {
		final Term constant = script.term("-", mConstant);
		final Map<IProgramVar, Term> coefficients = new HashMap<>(mCoefficients.size());
		for (final Map.Entry<IProgramVar, Term> entry : mCoefficients.entrySet()) {
			coefficients.put(entry.getKey(), script.term("-", entry.getValue()));
		}
		return new AffineFunctionGenerator(constant, coefficients);
	}
}
