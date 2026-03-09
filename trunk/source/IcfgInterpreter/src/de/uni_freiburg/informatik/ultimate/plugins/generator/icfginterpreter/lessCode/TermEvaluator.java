package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.IcfgInterpreterObserver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramExecutions.Pair;

public class TermEvaluator {
	private static ValueToTermStorage cache = ValueToTermStorage.getInstance();

	public static Value evaluate(final Map<TermVariable, Value> state, final Term term) {
		switch (term) {
		case final ApplicationTerm a:
			return evaluateApplicationTerm(state, a);
		case final TermVariable tv:
			final Value value = state.get(tv);
			if (value == null) {
				throw new AssertionError("State does not contain vaiable " + tv.getName());
			}
			return value;
		case final ConstantTerm ct:
			return cache.getConstant(ct);
		case final QuantifiedFormula qf:
			IcfgInterpreterObserver.getLogger()
					.error("This plug-in does not handle quantified formulas.\n" + "Formula: " + qf.toStringDirect());
			//$FALL-THROUGH$
		default:
			throw new UnsupportedTermError();
		}
	}

	private static Pair<ArrayValue, List<Value>> unpackSelect(final Map<TermVariable, Value> state, final Term term) {
		final List<Value> keys = new ArrayList<>();
		Term arrayTerm = term;
		while (arrayTerm instanceof final ApplicationTerm at
				&& at.getFunction().getName().equals(SMTLIBConstants.SELECT)) {
			arrayTerm = at.getParameters()[0];

			final Term selectKey = at.getParameters()[1];
			keys.add(evaluate(state, selectKey));
		}
		if (evaluate(state, arrayTerm) instanceof final ArrayValue av) {
			return new Pair<>(av, keys);
		}
		return null;
	}

	private static Value evaluateApplicationTerm(final Map<TermVariable, Value> state, final ApplicationTerm aTerm) {
		Value value;
		IntValue intValue;
		BoolValue boolValue;
		final String operation = aTerm.getFunction().getName();

		/**** ------ ArraysEx ------ ****/
		switch (operation) {
		case "store":
			final Term arrayTerm = aTerm.getParameters()[0];
			final Value lastKey = evaluate(state, aTerm.getParameters()[1]);
			value = evaluate(state, aTerm.getParameters()[2]);

			// To store something at i of an array, the term (store (arrayT_1) key_1 value_1) is used.
			// If the underlying array is not 1 dimensional, then arrayT_1 is (select arrayT_2 key_2)
			// this continues until we have an array term that is a TermVariable.
			// we then do arrayT_N[key_N][key_N-1]...[key_1] = value_1
			final Pair<ArrayValue, List<Value>> resultSubSelect = unpackSelect(state, arrayTerm);
			final List<Value> keysPartial = resultSubSelect.b();
			keysPartial.addLast(lastKey);
			return resultSubSelect.a().store(keysPartial, value);

		case "select":
			final Pair<ArrayValue, List<Value>> resultSelect = unpackSelect(state, aTerm);
			return resultSelect.a().select(resultSelect.b());
		}

		// final Stream<Value> params = Arrays.stream(aTerm.getParameters()).map(x -> evaluate(state, x));

		final Term[] paramTerms = aTerm.getParameters();
		final Value[] params = new Value[paramTerms.length];
		for (int i = 0; i < paramTerms.length; i++) {
			params[i] = evaluate(state, paramTerms[i]);
		}

		switch (operation) {
		/**** ------ Ints ------ ****/
		case "-":
			intValue = (IntValue) params[0];
			if (params.length == 1) {
				// case of negation, return -X
				return intValue.negate();
			}
			// case of subtraction return X - Y - Z - ...
			for (int i = 1; i < params.length; i++) {
				intValue = intValue.subtract((IntValue) params[i]);
			}
			return intValue;
		case "+":
			intValue = (IntValue) params[0];
			for (int i = 1; i < params.length; i++) {
				intValue = intValue.add((IntValue) params[i]);
			}
			return intValue;
		case "*":
			intValue = (IntValue) params[0];
			for (int i = 1; i < params.length; i++) {
				intValue = intValue.multiply((IntValue) params[i]);
			}
			return intValue;
		case "div":
			intValue = (IntValue) params[0];
			for (int i = 1; i < params.length; i++) {
				intValue = intValue.div((IntValue) params[i]);
			}
			return intValue;
		case "mod":
			// not chainable / left/right-associative
			return ((IntValue) params[0]).mod((IntValue) params[1]);
		case "abs":
			// single param term
			return ((IntValue) params[0]).abs();
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
			return ((BoolValue) params[0]).not();
		case "=>":
			// right associative, params [a, b, c, d] means (a => (b => (c => d)))
			BoolValue rightSideElement = (BoolValue) params[params.length - 1];
			for (int i = params.length - 2; 0 <= i; i--) {
				rightSideElement = ((BoolValue) params[i]).implies(rightSideElement);
			}
			return rightSideElement;
		case "and":
			boolValue = (BoolValue) params[0];
			for (int i = 1; i < params.length; i++) {
				boolValue = boolValue.and((BoolValue) params[i]);
			}
			return boolValue;
		case "or":
			boolValue = (BoolValue) params[0];
			for (int i = 1; i < params.length; i++) {
				boolValue = boolValue.or((BoolValue) params[i]);
			}
			return boolValue;
		case "xor":
			boolValue = (BoolValue) params[0];
			for (int i = 1; i < params.length; i++) {
				boolValue = boolValue.xor((BoolValue) params[i]);
			}
			return boolValue;

		/**** ------ Generic ------ ****/

		case "=":
			// chainable
			value = params[0];
			for (int i = 1; i < params.length; i++) {
				if (!value.equals(params[i]).getValue()) {
					return BoolValue.mFalse;
				}
			}
			return BoolValue.mTrue;
		case "distinct":
			// pairwise
			final HashSet<Object> distinctValues = new HashSet<>();

			for (final Value param : params) {
				if (distinctValues.contains(param.getValue())) {
					return BoolValue.mFalse;
				}
				distinctValues.add(param.getValue());
			}
			return BoolValue.mTrue;
		case "ite":
			// three param term
			final BoolValue condition = (BoolValue) params[0];
			final Value a = params[1];
			final Value b = params[2];
			return condition.getValue() ? a : b;

		default:
			throw new UnsupportedTermError();
		}
	}

	public static class UnsupportedTermError extends AssertionError {
		public UnsupportedTermError(final String string) {
			super(string);
		}

		public UnsupportedTermError() {
		}

		private static final long serialVersionUID = 1L;

	}

	private static final BoolValue compareTo(final Value[] params,
			final BiFunction<IntValue, IntValue, BoolValue> comparison) {
		IntValue value = (IntValue) params[0];

		for (int i = 1; i < params.length; i++) {
			final IntValue nextValue = (IntValue) params[i];
			if (!comparison.apply(value, nextValue).getValue()) {
				return BoolValue.mFalse;
			}
			value = nextValue;
		}

		return BoolValue.mTrue;
	}
}
