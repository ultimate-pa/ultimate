package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;

public class TermEvaluator {
	public static Value evaluate(final Map<Term, Value> state, final Term term, final NonDeterministicChoice ndc) {
		switch (term) {
		case final ApplicationTerm a:
			return evaluateApplicationTerm(state, a, ndc);
		case final TermVariable tv:
			return state.get(tv);
		case final ConstantTerm ct:
			return evaluateConstantTerm(ct);
		default:
			throw new AssertionError();
		}
	}

	private static Value evaluateConstantTerm(final ConstantTerm termConst) {
		final Object valueUnparsed = termConst.getValue();
		final Sort sort = termConst.getSort();

		switch (sort.getName()) {
		case SMTLIBConstants.INT:
			BigInteger value;
			if (valueUnparsed instanceof final Rational rat && rat.denominator().equals(BigInteger.ONE)) {
				value = rat.numerator();
			} else if (valueUnparsed instanceof final BigInteger bi) {
				value = bi;
			} else {
				throw new AssertionError();
			}
			return new IntValue(value);
		case SMTLIBConstants.BOOL:
			return new BoolValue((boolean) valueUnparsed);

		case SMTLIBConstants.BITVEC:
			final int length = Integer.parseInt(sort.getIndices()[0]);
			return new BitVecValue((BigInteger) valueUnparsed, length);
		default:
			throw new AssertionError();
		}
	}

	private static Value evaluateApplicationTerm(final Map<Term, Value> state, final ApplicationTerm aTerm,
			final NonDeterministicChoice ndc) {
		final Stream<Value> params = Arrays.stream(aTerm.getParameters()).map(x -> evaluate(state, x, ndc));
		Iterator<Value> iter;
		IntValue intValue;
		Value value;
		switch (aTerm.getFunction().getName()) {
		/**** ------ Ints ------ ****/
		case "-":
			iter = params.iterator();
			intValue = (IntValue) iter.next();
			if (!iter.hasNext()) {
				// case of negation, return -X
				return intValue.negate();
			}
			// case of subtraction return X - Y - Z - ...
			while (iter.hasNext()) {
				intValue = intValue.subtract((IntValue) iter.next());
			}
			return intValue;
		case "+":
			return params.reduce(IntValue.ZERO, (x, y) -> ((IntValue) x).add((IntValue) y));
		case "*":
			return params.reduce(IntValue.ONE, (x, y) -> ((IntValue) x).multiply((IntValue) y));
		case "div":
			iter = params.iterator();
			intValue = (IntValue) iter.next();
			while (iter.hasNext()) {
				intValue = intValue.div((IntValue) iter.next());
			}
			return intValue;
		case "mod":
			// not chainable / left/right-associative
			iter = params.iterator();
			return ((IntValue) iter.next()).mod((IntValue) iter.next());
		case "abs":
			// single param term
			return ((IntValue) params.iterator().next()).abs();
		case "<=":
			return compareTo(params, (a, b) -> a.leq(b));
		case "<":
			return compareTo(params, (a, b) -> a.lss(b));
		case ">=":
			return compareTo(params, (a, b) -> a.geq(b));
		case ">":
			return compareTo(params, (a, b) -> a.gtr(b));

		/**** ------ Bool ------ ****/

		case "true":
			return BoolValue.mTrue;
		case "false":
			return BoolValue.mFalse;
		case "not":
			// single param term
			return ((BoolValue) params.iterator().next()).not();
		case "=>":
			// right associative, params [a, b, c, d] means (a => (b => (c => d)))
			final List<Value> paramList = params.toList();
			BoolValue rightSideElement = (BoolValue) paramList.getLast();
			for (int i = paramList.size() - 2; 0 <= i; i--) {
				rightSideElement = ((BoolValue) paramList.get(i)).implies(rightSideElement);
			}
			return rightSideElement;
		case "and":
			return params.reduce(BoolValue.mTrue, (x, y) -> ((BoolValue) x).and((BoolValue) y));
		case "or":
			return params.reduce(BoolValue.mFalse, (x, y) -> ((BoolValue) x).or((BoolValue) y));
		case "xor":
			return params.reduce(BoolValue.mFalse, (x, y) -> ((BoolValue) x).xor((BoolValue) y));

		/**** ------ ArraysEx ------ ****/

		case "store":
			// three param term
			iter = params.iterator();
			final ArrayValue storeArray = (ArrayValue) iter.next();
			final Value storeKey = iter.next();
			final Value storeValue = iter.next();
			return storeArray.store(storeKey, storeValue);
		case "select":
			// two param term
			iter = params.iterator();
			final ArrayValue selectArray = (ArrayValue) iter.next();
			final Value selectKey = iter.next();
			return selectArray.select(selectKey, ndc);

		/**** ------ Generic ------ ****/

		case "=":
			// chainable
			iter = params.iterator();
			value = iter.next();
			while (iter.hasNext()) {
				if (!value.equals(iter.next()).getValue()) {
					return BoolValue.mFalse;
				}
			}
			return BoolValue.mTrue;
		case "distinct":
			// pairwise
			final HashSet<Object> distinctValues = new HashSet<>();

			for (final Value param : params.toList()) {
				if (distinctValues.contains(param.getValue())) {
					return BoolValue.mFalse;
				}
				distinctValues.add(param.getValue());
			}
			return BoolValue.mTrue;
		case "ite":
			// three param term
			iter = params.iterator();
			final BoolValue condition = (BoolValue) iter.next();
			final Value a = iter.next();
			final Value b = iter.next();
			return condition.getValue() ? a : b;

		default:
			throw new UnsopportedTermError();
		}
	}

	public static class UnsopportedTermError extends AssertionError {

	}

	private static final BoolValue compareTo(final Stream<Value> params,
			final BiFunction<IntValue, IntValue, BoolValue> comparison) {
		final Iterator<Value> iter = params.iterator();
		IntValue value = (IntValue) iter.next();
		while (iter.hasNext()) {
			final IntValue nextValue = (IntValue) iter.next();
			if (!comparison.apply(value, nextValue).getValue()) {
				return BoolValue.mFalse;
			}
			value = nextValue;
		}
		return BoolValue.mTrue;
	}
}
