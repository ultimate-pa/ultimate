package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Map;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TermEvaluator {
	public interface Value {

	}

	public class IntValue implements Value {
		private final BigInteger mValue;

		public IntValue(final BigInteger value) {
			mValue = value;
		}

		public IntValue add(final Value other) {
			return new IntValue(mValue.add(((IntValue) other).mValue));
		}
	}

	public class BoolValue implements Value {

	}

	public Value evaluate(final Map<Term, Value> state, final Term term) {
		switch (term) {
		case final ApplicationTerm a:
			return evaluateApplicationTerm(state, a);
		case final TermVariable tv:
			return state.get(tv);
		default:
			throw new AssertionError();
		}
	}

	private Value evaluateApplicationTerm(final Map<Term, Value> state, final ApplicationTerm a) {
		final Stream<Value> params = Arrays.stream(a.getParameters()).map(x -> evaluate(state, x));
		switch (a.getFunction().getName()) {
		case "+":
			return params.reduce(new IntValue(BigInteger.ZERO), (x, y) -> ((IntValue) x).add(y));
		default:
			throw new AssertionError();
		}
	}
}
