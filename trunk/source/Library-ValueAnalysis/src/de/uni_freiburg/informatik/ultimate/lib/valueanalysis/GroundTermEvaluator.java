/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE ValueAnalysis Library.
 *
 * The ULTIMATE ValueAnalysis Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ValueAnalysis Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ValueAnalysis Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ValueAnalysis Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ValueAnalysis Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.valueanalysis;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.function.BinaryOperator;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.IConcreteValue.ArrayValue;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.IConcreteValue.BitvectorValue;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.IConcreteValue.BoolValue;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.IConcreteValue.NumberValue;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;

/**
 * Evaluates a {@link Term} to an {@link IConcreteValue} under a concrete value for each of its free variables, in
 * plain Java and without a solver. It only reads the term, it builds no new terms, so it is safe on any thread and
 * never grows the term's theory.
 * <p>
 * Supported are the core theory, linear and non-linear integer and real arithmetic, bitvectors and arrays. Anything
 * else throws {@link UnsupportedTermException}: uninterpreted functions of positive arity, quantifiers, floating point,
 * and the cases SMT-LIB leaves unspecified (integer and real division by zero).
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class GroundTermEvaluator {
	private final Map<TermVariable, IConcreteValue> mEnv;
	private final Map<String, IConcreteValue> mConstants;
	// Terms are DAGs; without the cache a heavily shared formula would be evaluated exponentially often.
	private final Map<Term, IConcreteValue> mCache = new IdentityHashMap<>();

	private GroundTermEvaluator(final Map<TermVariable, IConcreteValue> env,
			final Map<String, IConcreteValue> constants) {
		mEnv = env;
		mConstants = constants;
	}

	/**
	 * @param term
	 *            the term to evaluate
	 * @param env
	 *            a value for every free variable of {@code term}
	 * @param constants
	 *            a value for every 0-ary uninterpreted function (program constant) of {@code term}, by name
	 * @return the value of {@code term}
	 * @throws UnsupportedTermException
	 *             if the term contains something this evaluator cannot evaluate, or a variable without a value
	 */
	public static IConcreteValue evaluate(final Term term, final Map<TermVariable, IConcreteValue> env,
			final Map<String, IConcreteValue> constants) {
		return new GroundTermEvaluator(env, constants).eval(term);
	}

	/**
	 * @return the truth value of the Boolean {@code term}, see {@link #evaluate}
	 */
	public static boolean evaluateBoolean(final Term term, final Map<TermVariable, IConcreteValue> env,
			final Map<String, IConcreteValue> constants) {
		return asBool(evaluate(term, env, constants));
	}

	/**
	 * Solves {@code term = value} for {@code target}, which occurs exactly once in {@code term}, by inverting the
	 * operations on the way from the root of {@code term} to {@code target}: addition, subtraction, negation,
	 * multiplication by a constant, {@code to_real}, Boolean negation, and their bitvector counterparts as far as they
	 * are bijective.
	 *
	 * @param env
	 *            a value for every free variable of {@code term} other than {@code target}
	 * @return the value of {@code target} that makes {@code term} evaluate to {@code value}
	 * @throws UnsupportedTermException
	 *             if an operation on the way cannot be inverted, or no value of {@code target}'s sort solves it
	 */
	public static IConcreteValue solveFor(final Term term, final TermVariable target, final IConcreteValue value,
			final Map<TermVariable, IConcreteValue> env, final Map<String, IConcreteValue> constants) {
		return new GroundTermEvaluator(env, constants).invert(term, target, value);
	}

	private IConcreteValue invert(final Term term, final TermVariable target, final IConcreteValue value) {
		if (term == target) {
			return value;
		}
		if (term instanceof final AnnotatedTerm annotated) {
			return invert(annotated.getSubterm(), target, value);
		}
		if (!(term instanceof final ApplicationTerm app)) {
			throw new UnsupportedTermException("cannot invert " + term.getClass().getSimpleName());
		}
		final Term[] params = app.getParameters();
		int position = -1;
		for (int i = 0; i < params.length; i++) {
			if (Arrays.asList(params[i].getFreeVars()).contains(target)) {
				position = i;
				break;
			}
		}
		if (position < 0) {
			throw new UnsupportedTermException("target does not occur");
		}
		final Term inner = params[position];
		switch (app.getFunction().getName()) {
		case "+":
			return invert(inner, target, new NumberValue(asNumber(value).sub(sumExcept(params, position, -1))));
		case "-":
			if (params.length == 1) {
				return invert(inner, target, new NumberValue(asNumber(value).negate()));
			}
			if (position == 0) {
				return invert(inner, target, new NumberValue(asNumber(value).add(sumExcept(params, 0, -1))));
			}
			// a - ... - inner - ... = value
			return invert(inner, target, new NumberValue(
					number(params[0]).sub(asNumber(value)).sub(sumExcept(params, 0, position))));
		case "*": {
			Rational factor = Rational.ONE;
			for (int i = 0; i < params.length; i++) {
				if (i != position) {
					factor = factor.mul(number(params[i]));
				}
			}
			if (factor.signum() == 0) {
				throw new UnsupportedTermException("multiplication by zero");
			}
			final Rational quotient = asNumber(value).div(factor);
			if (SmtSortUtils.isIntSort(inner.getSort()) && !quotient.isIntegral()) {
				throw new UnsupportedTermException("no integer solution");
			}
			return invert(inner, target, new NumberValue(quotient));
		}
		case "to_real":
			if (!asNumber(value).isIntegral()) {
				throw new UnsupportedTermException("no integer solution");
			}
			return invert(inner, target, value);
		case "not":
			return invert(inner, target, BoolValue.of(!asBool(value)));
		case "bvadd": {
			BitvectorConstant result = asBitvector(value);
			for (int i = 0; i < params.length; i++) {
				if (i != position) {
					result = BitvectorConstant.bvsub(result, bitvector(params[i]));
				}
			}
			return invert(inner, target, new BitvectorValue(result));
		}
		case "bvsub":
			if (params.length != 2) {
				throw new UnsupportedTermException("n-ary bvsub");
			}
			return invert(inner, target, new BitvectorValue(position == 0
					? BitvectorConstant.bvadd(asBitvector(value), bitvector(params[1]))
					: BitvectorConstant.bvsub(bitvector(params[0]), asBitvector(value))));
		case "bvneg":
			return invert(inner, target, new BitvectorValue(BitvectorConstant.bvneg(asBitvector(value))));
		case "bvnot":
			return invert(inner, target, new BitvectorValue(BitvectorConstant.bvnot(asBitvector(value))));
		case "bvxor": {
			BitvectorConstant result = asBitvector(value);
			for (int i = 0; i < params.length; i++) {
				if (i != position) {
					result = BitvectorConstant.bvxor(result, bitvector(params[i]));
				}
			}
			return invert(inner, target, new BitvectorValue(result));
		}
		default:
			throw new UnsupportedTermException("cannot invert " + app.getFunction().getName());
		}
	}

	/**
	 * @return the sum of the numeric {@code params} except those at {@code skip1} and {@code skip2}
	 */
	private Rational sumExcept(final Term[] params, final int skip1, final int skip2) {
		Rational sum = Rational.ZERO;
		for (int i = 0; i < params.length; i++) {
			if (i != skip1 && i != skip2) {
				sum = sum.add(number(params[i]));
			}
		}
		return sum;
	}

	private static Rational asNumber(final IConcreteValue value) {
		if (value instanceof final NumberValue number) {
			return number.value();
		}
		throw new UnsupportedTermException("not a number: a " + value.getClass().getSimpleName());
	}

	private static BitvectorConstant asBitvector(final IConcreteValue value) {
		if (value instanceof final BitvectorValue bitvector) {
			return bitvector.value();
		}
		throw new UnsupportedTermException("not a bitvector: a " + value.getClass().getSimpleName());
	}

	private IConcreteValue eval(final Term term) {
		final IConcreteValue cached = mCache.get(term);
		if (cached != null) {
			return cached;
		}
		final IConcreteValue result = evalUncached(term);
		mCache.put(term, result);
		return result;
	}

	private IConcreteValue evalUncached(final Term term) {
		if (term instanceof final TermVariable tv) {
			final IConcreteValue value = mEnv.get(tv);
			if (value == null) {
				throw new UnsupportedTermException("no value for " + tv);
			}
			return value;
		}
		if (term instanceof final ConstantTerm constant) {
			return literal(constant);
		}
		if (term instanceof final AnnotatedTerm annotated) {
			return eval(annotated.getSubterm());
		}
		if (term instanceof final LetTerm let) {
			final Map<TermVariable, IConcreteValue> env = new HashMap<>(mEnv);
			final TermVariable[] vars = let.getVariables();
			final Term[] values = let.getValues();
			for (int i = 0; i < vars.length; i++) {
				env.put(vars[i], eval(values[i]));
			}
			return new GroundTermEvaluator(env, mConstants).eval(let.getSubTerm());
		}
		if (term instanceof final ApplicationTerm app) {
			return application(app);
		}
		throw new UnsupportedTermException("cannot evaluate " + term.getClass().getSimpleName());
	}

	private static IConcreteValue literal(final ConstantTerm constant) {
		if (SmtSortUtils.isNumericSort(constant.getSort())) {
			return new NumberValue(SmtUtils.toRational(constant));
		}
		if (SmtSortUtils.isBitvecSort(constant.getSort())) {
			return new BitvectorValue(BitvectorUtils.constructBitvectorConstant(constant));
		}
		throw new UnsupportedTermException("literal of sort " + constant.getSort());
	}

	private IConcreteValue application(final ApplicationTerm app) {
		final FunctionSymbol fun = app.getFunction();
		final Term[] params = app.getParameters();
		if (!fun.isIntern()) {
			if (params.length == 0) {
				final IConcreteValue value = mConstants.get(fun.getName());
				if (value != null) {
					return value;
				}
			}
			throw new UnsupportedTermException("uninterpreted function " + fun.getName());
		}
		if (BitvectorUtils.isBitvectorConstant(fun)) {
			return new BitvectorValue(BitvectorUtils.constructBitvectorConstant(app));
		}
		switch (fun.getName()) {
		// core
		case "true":
			return BoolValue.TRUE;
		case "false":
			return BoolValue.FALSE;
		case "not":
			return BoolValue.of(!bool(params[0]));
		case "and":
			for (final Term param : params) {
				if (!bool(param)) {
					return BoolValue.FALSE;
				}
			}
			return BoolValue.TRUE;
		case "or":
			for (final Term param : params) {
				if (bool(param)) {
					return BoolValue.TRUE;
				}
			}
			return BoolValue.FALSE;
		case "=>":
			// right associative: (=> a b c) is a => (b => c)
			for (int i = 0; i < params.length - 1; i++) {
				if (!bool(params[i])) {
					return BoolValue.TRUE;
				}
			}
			return BoolValue.of(bool(params[params.length - 1]));
		case "xor": {
			boolean result = false;
			for (final Term param : params) {
				result ^= bool(param);
			}
			return BoolValue.of(result);
		}
		case "=": {
			final IConcreteValue first = eval(params[0]);
			for (int i = 1; i < params.length; i++) {
				if (!first.equals(eval(params[i]))) {
					return BoolValue.FALSE;
				}
			}
			return BoolValue.TRUE;
		}
		case "distinct": {
			final IConcreteValue[] values = new IConcreteValue[params.length];
			for (int i = 0; i < params.length; i++) {
				values[i] = eval(params[i]);
				for (int j = 0; j < i; j++) {
					if (values[i].equals(values[j])) {
						return BoolValue.FALSE;
					}
				}
			}
			return BoolValue.TRUE;
		}
		case "ite":
			return bool(params[0]) ? eval(params[1]) : eval(params[2]);
		// arithmetic
		case "+":
			return foldNumbers(params, Rational::add);
		case "-":
			if (params.length == 1) {
				return new NumberValue(number(params[0]).negate());
			}
			return foldNumbers(params, Rational::sub);
		case "*":
			return foldNumbers(params, Rational::mul);
		case "/":
			return foldNumbers(params, GroundTermEvaluator::realDivision);
		case "div":
			return foldNumbers(params, (a, b) -> integral(euclideanDiv(integer(a), integer(b))));
		case "mod":
			return foldNumbers(params, (a, b) -> integral(euclideanMod(integer(a), integer(b))));
		case "abs":
			return new NumberValue(number(params[0]).abs());
		case "<":
			return compareChain(params, c -> c < 0);
		case "<=":
			return compareChain(params, c -> c <= 0);
		case ">":
			return compareChain(params, c -> c > 0);
		case ">=":
			return compareChain(params, c -> c >= 0);
		case "to_real":
			return new NumberValue(number(params[0]));
		case "to_int":
			return new NumberValue(number(params[0]).floor());
		case "is_int":
			return BoolValue.of(number(params[0]).isIntegral());
		case "divisible": {
			final BigInteger divisor = new BigInteger(fun.getIndices()[0]);
			return BoolValue.of(integer(number(params[0])).mod(divisor).signum() == 0);
		}
		// arrays
		case "select":
			return array(params[0]).select(eval(params[1]));
		case "store":
			return array(params[0]).store(eval(params[1]), eval(params[2]));
		case "const":
			return ArrayValue.constant(eval(params[0]));
		default:
			return bitvectorApplication(fun, params);
		}
	}

	private IConcreteValue bitvectorApplication(final FunctionSymbol fun, final Term[] params) {
		switch (fun.getName()) {
		case "bvadd":
			return foldBitvectors(params, BitvectorConstant::bvadd);
		case "bvsub":
			return foldBitvectors(params, BitvectorConstant::bvsub);
		case "bvmul":
			return foldBitvectors(params, BitvectorConstant::bvmul);
		case "bvand":
			return foldBitvectors(params, BitvectorConstant::bvand);
		case "bvor":
			return foldBitvectors(params, BitvectorConstant::bvor);
		case "bvxor":
			return foldBitvectors(params, BitvectorConstant::bvxor);
		case "bvudiv":
			return foldBitvectors(params, BitvectorConstant::bvudiv);
		case "bvurem":
			return foldBitvectors(params, BitvectorConstant::bvurem);
		case "bvsdiv":
			return foldBitvectors(params, GroundTermEvaluator::bvsdiv);
		case "bvsrem":
			// BitvectorConstant answers bvsrem s 0 = s, as SMT-LIB defines it
			return foldBitvectors(params, BitvectorConstant::bvsrem);
		case "bvsmod":
			return foldBitvectors(params, GroundTermEvaluator::bvsmod);
		case "bvshl":
			return foldBitvectors(params, BitvectorConstant::bvshl);
		case "bvlshr":
			return foldBitvectors(params, BitvectorConstant::bvlshr);
		case "bvashr":
			return foldBitvectors(params, BitvectorConstant::bvashr);
		case "concat":
			return foldBitvectors(params, BitvectorConstant::concat);
		case "bvnot":
			return new BitvectorValue(BitvectorConstant.bvnot(bitvector(params[0])));
		case "bvneg":
			return new BitvectorValue(BitvectorConstant.bvneg(bitvector(params[0])));
		case "bvult":
			return BoolValue.of(BitvectorConstant.bvult(bitvector(params[0]), bitvector(params[1])));
		case "bvule":
			return BoolValue.of(BitvectorConstant.bvule(bitvector(params[0]), bitvector(params[1])));
		case "bvugt":
			return BoolValue.of(BitvectorConstant.bvugt(bitvector(params[0]), bitvector(params[1])));
		case "bvuge":
			return BoolValue.of(BitvectorConstant.bvuge(bitvector(params[0]), bitvector(params[1])));
		case "bvslt":
			return BoolValue.of(BitvectorConstant.bvslt(bitvector(params[0]), bitvector(params[1])));
		case "bvsle":
			return BoolValue.of(BitvectorConstant.bvsle(bitvector(params[0]), bitvector(params[1])));
		case "bvsgt":
			return BoolValue.of(BitvectorConstant.bvsgt(bitvector(params[0]), bitvector(params[1])));
		case "bvsge":
			return BoolValue.of(BitvectorConstant.bvsge(bitvector(params[0]), bitvector(params[1])));
		case "bvcomp":
			return new BitvectorValue(new BitvectorConstant(
					bitvector(params[0]).equals(bitvector(params[1])) ? BigInteger.ONE : BigInteger.ZERO,
					BigInteger.ONE));
		case "extract": {
			final String[] indices = fun.getIndices();
			return new BitvectorValue(BitvectorConstant.extract(bitvector(params[0]), Integer.parseInt(indices[0]),
					Integer.parseInt(indices[1])));
		}
		case "zero_extend":
			return new BitvectorValue(
					BitvectorConstant.zero_extend(bitvector(params[0]), new BigInteger(fun.getIndices()[0])));
		case "sign_extend":
			return new BitvectorValue(
					BitvectorConstant.sign_extend(bitvector(params[0]), new BigInteger(fun.getIndices()[0])));
		default:
			throw new UnsupportedTermException("function " + fun.getName());
		}
	}

	/**
	 * SMT-LIB's bvsdiv, which for a zero divisor is all ones for a non-negative dividend and one for a negative one.
	 * {@link BitvectorConstant#bvsdiv} answers all ones for both.
	 */
	private static BitvectorConstant bvsdiv(final BitvectorConstant dividend, final BitvectorConstant divisor) {
		if (divisor.getValue().signum() == 0) {
			return new BitvectorConstant(dividend.toSignedInt().signum() < 0 ? BigInteger.ONE : BigInteger.ONE.negate(),
					dividend.getIndex());
		}
		return BitvectorConstant.bvsdiv(dividend, divisor);
	}

	/**
	 * SMT-LIB's bvsmod: the remainder of the floored division, whose sign follows the divisor, and the dividend for a
	 * zero divisor. {@link BitvectorConstant#bvsmod} gets both a zero remainder of a negative dividend and a zero
	 * divisor wrong.
	 */
	private static BitvectorConstant bvsmod(final BitvectorConstant dividend, final BitvectorConstant divisor) {
		final BigInteger s = dividend.toSignedInt();
		final BigInteger t = divisor.toSignedInt();
		if (t.signum() == 0) {
			return dividend;
		}
		BigInteger remainder = s.mod(t.abs());
		if (t.signum() < 0 && remainder.signum() != 0) {
			remainder = remainder.add(t);
		}
		return new BitvectorConstant(remainder, dividend.getIndex());
	}

	private static Rational realDivision(final Rational dividend, final Rational divisor) {
		if (divisor.signum() == 0) {
			throw new UnsupportedTermException("division by zero");
		}
		return dividend.div(divisor);
	}

	/**
	 * SMT-LIB's integer div: the q with dividend = divisor * q + r and 0 <= r < |divisor|.
	 */
	private static BigInteger euclideanDiv(final BigInteger dividend, final BigInteger divisor) {
		return dividend.subtract(euclideanMod(dividend, divisor)).divide(divisor);
	}

	/**
	 * SMT-LIB's integer mod, which is never negative.
	 */
	private static BigInteger euclideanMod(final BigInteger dividend, final BigInteger divisor) {
		if (divisor.signum() == 0) {
			throw new UnsupportedTermException("division by zero");
		}
		return dividend.mod(divisor.abs());
	}

	private static Rational integral(final BigInteger value) {
		return Rational.valueOf(value, BigInteger.ONE);
	}

	private static BigInteger integer(final Rational value) {
		if (!value.isIntegral()) {
			throw new UnsupportedTermException("integer operation on " + value);
		}
		return value.numerator();
	}

	private interface Comparison {
		boolean holds(int comparison);
	}

	private IConcreteValue compareChain(final Term[] params, final Comparison comparison) {
		Rational previous = number(params[0]);
		for (int i = 1; i < params.length; i++) {
			final Rational current = number(params[i]);
			if (!comparison.holds(previous.compareTo(current))) {
				return BoolValue.FALSE;
			}
			previous = current;
		}
		return BoolValue.TRUE;
	}

	private IConcreteValue foldNumbers(final Term[] params, final BinaryOperator<Rational> operation) {
		Rational result = number(params[0]);
		for (int i = 1; i < params.length; i++) {
			result = operation.apply(result, number(params[i]));
		}
		return new NumberValue(result);
	}

	private IConcreteValue foldBitvectors(final Term[] params, final BinaryOperator<BitvectorConstant> operation) {
		BitvectorConstant result = bitvector(params[0]);
		for (int i = 1; i < params.length; i++) {
			result = operation.apply(result, bitvector(params[i]));
		}
		return new BitvectorValue(result);
	}

	private boolean bool(final Term term) {
		return asBool(eval(term));
	}

	private Rational number(final Term term) {
		if (eval(term) instanceof final NumberValue number) {
			return number.value();
		}
		throw new UnsupportedTermException("not a number: a term of sort " + term.getSort());
	}

	private BitvectorConstant bitvector(final Term term) {
		if (eval(term) instanceof final BitvectorValue bitvector) {
			return bitvector.value();
		}
		throw new UnsupportedTermException("not a bitvector: a term of sort " + term.getSort());
	}

	private ArrayValue array(final Term term) {
		if (eval(term) instanceof final ArrayValue array) {
			return array;
		}
		throw new UnsupportedTermException("not an array: a term of sort " + term.getSort());
	}

	private static boolean asBool(final IConcreteValue value) {
		if (value instanceof final BoolValue bool) {
			return bool.value();
		}
		throw new UnsupportedTermException("not a Boolean: a " + value.getClass().getSimpleName());
	}
}
