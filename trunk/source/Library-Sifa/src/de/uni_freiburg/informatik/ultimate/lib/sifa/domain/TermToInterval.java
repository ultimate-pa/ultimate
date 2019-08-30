/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Converts a term into one (!) interval. Before evaluation intervals can be assigned to variables.
 * Examples:
 * <ul>
 * <li> 1 evaluates to [1, 1].
 * <li> 1 + 2 evaluates to [3, 3].
 * <li> x evaluates to the given interval for x or [-inf, inf] if no interval was given for this variable.
 * <li> evaluating 1 == 2 throws an exception
 * </ul>
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public final class TermToInterval {

	private TermToInterval() {
		// objects of this class have no purpose
	}

	// TODO should we use caching as in TermTransformer? (when implementing, watch out for changing scopes)

	// TODO use quantifier elimination in here or in IntervalDomain as post(x := x / y) introduces quantifiers

	/**
	 * Evaluates a term using interval arithmetic.
	 * @param term The term to be evaluated
	 * @param scope Already known values for some variables
	 * @return Result of the given term according to interval arithmetic
	 */
	public static Interval evaluate(final Term term, final Map<TermVariable, Interval> scope) {
		if (!term.getSort().isNumericSort()) {
			throw new IllegalArgumentException("Tried to use intervals for non-numeric sort: " + term);
		} else if (term instanceof ApplicationTerm) {
			return evaluate((ApplicationTerm) term, scope);
		} else if (term instanceof LetTerm) {
			return evaluate((LetTerm) term, scope);
		} else if (term instanceof AnnotatedTerm) {
			return evaluate((AnnotatedTerm) term, scope);
		} else if (term instanceof QuantifiedFormula) {
			return evaluate((QuantifiedFormula) term, scope);
		} else if (term instanceof ConstantTerm) {
			return evaluate((ConstantTerm) term, scope);
		} else if (term instanceof TermVariable) {
			return evaluate((TermVariable) term, scope);
		}
		throw new UnsupportedOperationException("Could not process term of unknown type: " + term);
	}

	private static Interval evaluate(final ConstantTerm term, final Map<TermVariable, Interval> scope) {
		final Object value = term.getValue();
		if (value instanceof Rational) {
			return Interval.point((Rational) value);
		} else if (value instanceof BigInteger) {
			return Interval.point(SmtUtils.toRational((BigInteger) value));
		} else if (value instanceof BigDecimal) {
			return Interval.point(SmtUtils.toRational((BigDecimal) value));
		}
		return Interval.TOP;
	}

	private static Interval evaluate(final TermVariable term, final Map<TermVariable, Interval> scope) {
		return scope.getOrDefault(term, Interval.TOP);
	}

	private static Interval evaluate(final AnnotatedTerm term, final Map<TermVariable, Interval> scope) {
		// TODO are there any annotations we have to consider?
		return evaluate(term.getSubterm(), scope);
	}

	private static Interval evaluate(final LetTerm term, final Map<TermVariable, Interval> outerScope) {
		// IScopedMap could be used with an intermediate map, but using a completely new map is easier
		final HashMap<TermVariable, Interval> innerScope = new HashMap<>(outerScope);
		final TermVariable[] letVariables = term.getVariables();
		final Term[] letValues = term.getValues();
		assert letVariables.length == letValues.length : "Number of variables and values does not match: " + term;
		for (int letIndex = 0; letIndex < letVariables.length; ++letIndex) {
			// TODO ignore variables whose values cannot be represented by intervals
			innerScope.put(letVariables[letIndex], evaluate(letValues[letIndex], outerScope));
		}
		return evaluate(term.getSubTerm(), innerScope);
	}

	private static Interval evaluate(final QuantifiedFormula term, final Map<TermVariable, Interval> scope) {
		throw new UnsupportedOperationException("Bool cannot be expressed as an interval.");
	}

	private static Interval evaluate(final ApplicationTerm term, final Map<TermVariable, Interval> scope) {
		final int arity = term.getParameters().length;
		if (arity < 1) {
			return Interval.TOP;
		} else if (arity == 1) {
			return handleUnaryFunction(term, scope);
		} else {
			return handleGEq2AryFunction(term, scope);
		}
	}

	private static Interval handleUnaryFunction(final ApplicationTerm term, final Map<TermVariable, Interval> scope) {
		assert term.getParameters().length == 1 : "Expected unary function but found " + term;
		if (isFunction("-", term)) {
			final Term param = term.getParameters()[0];
			return evaluate(param, scope).negate();
		} else {
			return Interval.TOP;
		}
	}

	/** Evaluates functions of arity greater or equal 2. */
	private static Interval handleGEq2AryFunction(final ApplicationTerm term, final Map<TermVariable, Interval> scope) {
		if (isFunction("ite", term)) {
			return handleIfThenElseFunction(term, scope);
		} else {
			return handleLeftAssociativeFunction(term, scope);
		}
	}

	private static Interval handleIfThenElseFunction(final ApplicationTerm term,
			final Map<TermVariable, Interval> scope) {
		final Term[] iteParams = term.getParameters();
		assert isFunction("ite", term) : "Expected ite term but found " + term;
		assert iteParams.length == 3 : "Expected 3 parameters for ite term but found " + term;
		// TODO evaluate condition (condition is boolean, but we only support numeric types in intervals)
		// For now we ignore the condition and over-approximate
		final Interval iteThenResult = evaluate(iteParams[1], scope);
		final Interval iteElseResult = evaluate(iteParams[2], scope);
		return iteThenResult.union(iteElseResult);
	}

	private static boolean isFunction(final String functionName, final ApplicationTerm term) {
		return functionName.equals(term.getFunction().getName());
	}

	private static Interval handleLeftAssociativeFunction(final ApplicationTerm term,
			final Map<TermVariable, Interval> scope) {
		final BiFunction<Interval, Interval, Interval> leftAssociativeOp =
				intervalOpForSmtFunc(term.getFunction().getName());
		if (leftAssociativeOp == null) {
			return Interval.TOP;
		}
		final Term[] params = term.getParameters();
		assert params.length >= 2 : "Expected n-ary function with n >= 2 but found " + term;
		Interval accumulator = evaluate(params[0], scope);
		for (int paramIdx = 1; paramIdx < params.length; ++paramIdx) {
			accumulator = leftAssociativeOp.apply(accumulator, evaluate(params[paramIdx], scope));
			// We cannot use a shortcut, even for an intermediate TOP result.
			// A BOTTOM result of the last parameter will turn everything to BOTTOM.
		}
		return accumulator;
	}

	private static BiFunction<Interval, Interval, Interval> intervalOpForSmtFunc(final String functionName) {
		switch (functionName) {
		case "+":
			return Interval::add;
		case "-":
			return Interval::subtract;
		case "*":
			return Interval::multiply;
		case "/":
			return Interval::divide;
		default:
			return null;
		}
	}

}
