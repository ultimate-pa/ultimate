/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Map;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
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
 * <li> TODO document what happends for terms of non-numeric sort
 * </ul>
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class TermToInterval extends NonRecursive {

	private final ArrayDeque<Interval> mReturnedResultsStack = new ArrayDeque<>();

	/**
	 * Maps variables to intervals containing all the values these variables can assume.
	 * It is ok to leave out variables of unknown value.
	 * This field is set and unset with each call of {@link #evaluate(Term)}.
	 */
	private Map<TermVariable, Interval> mValues;

	/**
	 * TODO document this is not thread save, just like every other NonRecursive.doYourStuff()
	 */
	public Interval evaluate(final Term term, final Map<TermVariable, Interval> knownValues) {
		mValues = knownValues;
		run(new Evaluator(term));
		// We don't need the map anymore -- we get a new one with each call.
		// Make sure the garbage collector has a chance to get rid of it.
		mValues = null;
		return retrieveReturnValue();
	}

	private void returnValue(final Interval result) {
		mReturnedResultsStack.addLast(result);
	}

	private Interval retrieveReturnValue() {
		return mReturnedResultsStack.removeLast();
	}

	private Interval valueOf(final TermVariable var) {
		return mValues.getOrDefault(var, Interval.TOP);
	}

	private class Evaluator extends TermWalker {

		public Evaluator(final Term term) {
			super(term);
			if (!mTerm.getSort().isNumericSort()) {
				throw new IllegalArgumentException("Tried to use intervals for non-numeric sort: " + mTerm);
			}
		}

		@Override
		public void walk(final NonRecursive term2Ivl, final ConstantTerm term) {
			final Object value = term.getValue();
			if (value instanceof Rational) {
				returnValue(Interval.point((Rational) value));
			} else if (value instanceof BigInteger) {
				returnValue(Interval.point(SmtUtils.toRational((BigInteger) value)));
			} else if (value instanceof BigDecimal) {
				returnValue(Interval.point(SmtUtils.toRational((BigDecimal) value)));
			} else {
				returnValue(Interval.TOP);
			}
		}

		@Override
		public void walk(final NonRecursive term2Ivl, final AnnotatedTerm term) {
			enqueueWalker(new Evaluator(term.getSubterm()));
			// no need for returnResult as we didn't call retrieveResult
		}

		@Override
		public void walk(final NonRecursive term2Ivl, final ApplicationTerm term) {
			final int arity = term.getParameters().length;
			if (arity < 1) {
				returnValue(Interval.TOP);
			} else if (arity == 1) {
				handleUnaryFunction(term2Ivl, term);
			} else {
				handleNAryFunction(term2Ivl, term);
			}
		}

		private void handleUnaryFunction(final NonRecursive term2Ivl, final ApplicationTerm term) {
			assert term.getParameters().length == 1 : "Expected unary function but found " + term;
			if ("-".equals(term.getFunction().getName())) {
				final Term param = term.getParameters()[0];
				returnValue(evaluate(param).negate());
			} else {
				returnValue(Interval.TOP);
			}
		}

		private void handleNAryFunction(final NonRecursive term2Ivl, final ApplicationTerm term) {
			final BiFunction<Interval, Interval, Interval> leftAssociativeOp =
					intervalOpForSmtFunc(term.getFunction().getName());
			if (leftAssociativeOp == null) {
				returnValue(Interval.TOP);
				return;
			}
			final Term[] params = term.getParameters();
			assert params.length >= 2 : "Expected n-ary function with n >= 2 but found " + term;
			Interval accumulator = evaluate(params[0]);
			for (int paramIdx = 1; paramIdx < params.length; ++paramIdx) {
				accumulator = leftAssociativeOp.apply(accumulator, evaluate(params[paramIdx]));
				// We cannot use a shortcut, even for an intermediate TOP result.
				// A BOTTOM result of the last parameter will turn everything to BOTTOM.
			}
			returnValue(accumulator);
		}

		private Interval evaluate(final Term term) {
			enqueueWalker(new Evaluator(term));
			// TODO ERROR BUG !!! This will not work as expected. enqueueWalker runs AFTER this function
			return retrieveReturnValue();
		}

		private BiFunction<Interval, Interval, Interval> intervalOpForSmtFunc(final String functionName) {
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

		@Override
		public void walk(final NonRecursive term2Ivl, final LetTerm term) {
			throw new IllegalArgumentException("Let terms not supported yet");
			// TODO add scoped map or something like this, calculate value, put it in map, continue evaluation
		}

		@Override
		public void walk(final NonRecursive term2Ivl, final QuantifiedFormula term) {
			returnValue(Interval.TOP);
		}

		@Override
		public void walk(final NonRecursive term2Ivl, final TermVariable term) {
			returnValue(valueOf(term));
		}
	}

}
