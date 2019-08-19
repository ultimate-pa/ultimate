/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Collection of random utility functions.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Claus Schätzle (schaetzc@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public final class AbsIntUtil {

	public static final BigDecimal MINUS_ONE = BigDecimal.ONE.negate();
	public static final BigDecimal TWO = new BigDecimal(2);

	private AbsIntUtil() {
		// do not instantiate utility class
	}

	/**
	 * Write predicates created by AI to a file.
	 *
	 * @param preds
	 * @param filePath
	 */
	public static void dumpToFile(final Map<CodeBlock, Map<BoogieIcfgLocation, Term>> preds, final String filePath) {
		final StringBuilder sb = new StringBuilder();
		for (final Entry<CodeBlock, Map<BoogieIcfgLocation, Term>> entry : preds.entrySet()) {
			if (entry.getValue().isEmpty()) {
				continue;
			}
			sb.append(entry.getKey().toString()).append("\n");
			for (final Entry<BoogieIcfgLocation, Term> runPreds : entry.getValue().entrySet()) {
				sb.append(" * ").append(runPreds.getValue()).append("\n");
			}
		}
		if (sb.length() == 0) {
			sb.append("No preds :(\n");
		}

		sb.append("\n\n");
		try (final BufferedWriter bw = new BufferedWriter(new FileWriter(filePath, true))) {
			bw.append(sb);
			bw.close();
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
	}

	public static <LOC> void logPredicates(final Map<?, Map<LOC, Term>> preds, final Script script,
			final Consumer<String> printer) {
		final Map<LOC, Term> predsPerLoc = new HashMap<>();
		for (final Entry<?, Map<LOC, Term>> entryPerBlock : preds.entrySet()) {
			for (final Entry<LOC, Term> entryPerLoc : entryPerBlock.getValue().entrySet()) {
				final Term current = predsPerLoc.get(entryPerLoc.getKey());
				if (current == null) {
					predsPerLoc.put(entryPerLoc.getKey(), entryPerLoc.getValue());
				} else {
					predsPerLoc.put(entryPerLoc.getKey(), SmtUtils.or(script, entryPerLoc.getValue(), current));
				}
			}
		}
		logPredicates(predsPerLoc, printer);
	}

	public static void logPredicates(final Map<?, Term> preds, final Consumer<String> printer) {
		for (final Entry<?, Term> entry : preds.entrySet()) {
			printer.accept(entry.getKey() + ": " + entry.getValue());
		}
	}

	public static <K, V> Map<K, V> getFreshMap(final Map<K, V> oldMap, final int capacity) {
		final Map<K, V> rtr = new HashMap<>(capacity);
		rtr.putAll(oldMap);
		return rtr;
	}

	public static <K, V> Map<K, V> getFreshMap(final Map<K, V> oldMap) {
		return getFreshMap(oldMap, oldMap.size());
	}

	public static <T> ArrayList<T> singletonArrayList(final T value) {
		final ArrayList<T> list = new ArrayList<>();
		list.add(value);
		return list;
	}

	/**
	 * Calculates the euclidean division.euc The result {@code q} of the euclidean division {@code a / b = q} satisfies
	 * {@code a = bq + r} where {@code 0 ≤ r < |b|} and {@code b ≠ 0}.
	 * <p>
	 * The type of division only matters for non-real numbers like integers or floats with limited precision.
	 * <p>
	 * Examples:<br>
	 * <code>
	 *     +7 / +3 = +2<br>
	 *     +7 / -3 = -2<br>
	 *     -7 / +3 = -3<br>
	 *     -7 / -3 = +3
	 * </code>
	 *
	 * @param a
	 *            dividend
	 * @param b
	 *            divisor
	 * @return euclidean division {@code q = a / b}
	 *
	 * @throws ArithmeticException
	 *             if {@code b = 0}
	 */
	public static BigDecimal euclideanDivision(final BigDecimal a, final BigDecimal b) {
		final BigDecimal[] quotientAndRemainder = a.divideAndRemainder(b);
		BigDecimal quotient = quotientAndRemainder[0];
		final BigDecimal remainder = quotientAndRemainder[1];
		if (remainder.signum() != 0 && a.signum() < 0) {
			// sig(a) != 0, since "remainder != 0"
			if (b.signum() < 0) {
				// sig(b) != 0, since "a / 0" throws an exception
				quotient = quotient.add(BigDecimal.ONE);
			} else {
				quotient = quotient.subtract(BigDecimal.ONE);
			}
		}
		return quotient;
	}

	public static Rational euclideanDivision(final Rational a, final Rational b) {
		Rational quotient = a.div(b);
		if (quotient.signum() == -1) {
			quotient = quotient.ceil();
		} else {
			quotient = quotient.floor();
		}
		final Rational remainder = a.sub(quotient.mul(b));

		if (remainder.signum() != 0 && a.signum() < 0) {
			// sig(a) != 0, since "remainder != 0"
			if (b.signum() < 0) {
				// sig(b) != 0, since "a / 0" throws an exception
				quotient = quotient.add(Rational.ONE);
			} else {
				quotient = quotient.sub(Rational.ONE);
			}
		}
		return quotient;

	}

	/**
	 * Calculates {@code a / b} only if {@code b} is a divisor of {@code a}.
	 *
	 * @param a
	 *            dividend
	 * @param b
	 *            true divisor of {@code a}
	 * @return exact result of {@code a / b} (always an integer)
	 *
	 * @throws ArithmeticException
	 *             if {@code b} is a not a divisor of {@code a}.
	 */
	public static BigDecimal exactDivison(final BigDecimal a, final BigDecimal b) {
		final BigDecimal[] quotientAndRemainder = a.divideAndRemainder(b);
		if (quotientAndRemainder[1].signum() == 0) {
			return quotientAndRemainder[0];
		}
		throw new ArithmeticException("Divison not exact for " + a + " / " + b);
	}

	public static Rational exactDivision(final Rational a, final Rational b) {
		final Rational divisionResult = a.div(b);
		if (divisionResult.isIntegral()) {
			return divisionResult;
		}
		throw new ArithmeticException("Divison not exact for " + a + " / " + b);
	}

	/**
	 * Checks if a number is integral.
	 *
	 * @param d
	 *            number
	 * @return {@code d} is an integer
	 */
	public static boolean isIntegral(final BigDecimal d) {
		return d.remainder(BigDecimal.ONE).signum() == 0;
	}

	/**
	 * Calculates the euclidean modulo. The result {@code r} is the remainder of the euclidean division
	 * {@code a / b = q}, satisfying {@code a = bq + r} where {@code 0 ≤ r < |b|} and {@code b ≠ 0}.
	 * <p>
	 * Examples:<br>
	 * <code>
	 *     +7 % +3 = 1<br>
	 *     +7 % -3 = 1<br>
	 *     -7 % +3 = 2<br>
	 *     -7 % -3 = 2
	 * </code>
	 *
	 * @param a
	 *            dividend
	 * @param b
	 *            divisor
	 * @return {@code r = a % b} (remainder of the euclidean division {@code a / b})
	 *
	 * @throws ArithmeticException
	 *             if {@code b = 0}
	 */
	public static BigDecimal euclideanModulo(final BigDecimal a, final BigDecimal b) {
		BigDecimal r = a.remainder(b);
		if (r.signum() < 0) {
			r = r.add(b.abs());
		}
		return r;
	}

	/**
	 * As {@link AbsIntUtil#euclideanModulo(BigDecimal, BigDecimal)}, but for {@link BigInteger}
	 */
	public static BigInteger euclideanModulo(final BigInteger a, final BigInteger b) {
		BigInteger r = a.remainder(b);
		if (r.signum() < 0) {
			r = r.add(b.abs());
		}
		return r;
	}

	public static Rational euclideanModulo(final Rational a, final Rational b) {
		final Rational divisionResult = a.div(b);
		final Rational floor = divisionResult.floor();
		final Rational remainder = a.sub(floor.mul(b));
		if (remainder.isNegative()) {
			return remainder.add(b.abs());
		}
		return remainder;
	}

	/**
	 * Turns a BigDecimal d into its decimal fraction d = numerator / denominator. Numerator and denominator are both
	 * integers and denominator is a positive power of 10. Trailing zeros are not removed (can be done by
	 * {@link BigDecimal#stripTrailingZeros()} in advance).
	 * <p>
	 * Examples:<br>
	 *
	 * <pre>
	 *  1.5   =  15 /   10
	 * -1.5   = -15 /   10
	 * 20.0   = 200 /   10
	 * 20     =  20 /    1
	 *  2e1   =  20 /    1
	 *  0.03  =   3 /  100
	 *  0.030 =  30 / 1000
	 *  0e9   =   0 /    1
	 * </pre>
	 *
	 * @param d
	 *            BigDecimal
	 * @return decimal fraction
	 */
	public static Pair<BigInteger, BigInteger> decimalFraction(final BigDecimal d) {
		BigInteger numerator = d.unscaledValue();
		BigInteger denominator = BigInteger.TEN.pow(Math.abs(d.scale()));
		if (d.scale() < 0) {
			numerator = numerator.multiply(denominator);
			denominator = BigInteger.ONE;
		}
		return new Pair<>(numerator, denominator);
	}

	/**
	 * Creates a dummy {@link IProgramVar} from a given type. This method is used to give generated temporary variables
	 * a boogie type.
	 *
	 * @param identifier
	 *            the identifier of the variable
	 * @param type
	 *            the type of the variable
	 * @return {@link IProgramVar} according to the given identifier and {@link IBoogieType}
	 *
	 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
	 */
	public static IProgramVar createTemporaryIBoogieVar(final String identifier, final IBoogieType type) {
		return new FakeBoogieVar(type, identifier);
	}

	/**
	 * Determines if a {@link IdentifierExpression} references a variable or constant. {@link IdentifierExpression} can
	 * also reference functions or procedures. In that case, this method will return {@code false}.
	 *
	 * @param ie
	 *            {@link IdentifierExpression}
	 * @return expression references a variable or constant
	 */
	public static boolean isVariable(final IdentifierExpression ie) {
		final DeclarationInformation di = ie.getDeclarationInformation();
		switch (di.getStorageClass()) {
		case PROC_FUNC:
		case IMPLEMENTATION:
			return false;
		case GLOBAL:
		case IMPLEMENTATION_INPARAM:
		case IMPLEMENTATION_OUTPARAM:
		case LOCAL:
		case QUANTIFIED:
		case PROC_FUNC_INPARAM:
		case PROC_FUNC_OUTPARAM:
			return true;
		default:
			throw new IllegalArgumentException("Unknown storage class: " + di.getStorageClass());
		}
	}

	public static boolean isOldVar(final IProgramVarOrConst ibv) {
		return ibv instanceof IProgramOldVar;
	}

	public static boolean isGlobal(final IProgramVarOrConst ibv) {
		if (ibv instanceof IProgramVar) {
			return ibv.isGlobal();
		} else if (ibv instanceof BoogieConst) {
			return true;
		} else {
			throw new AssertionError("Unknown IProgramVar type: " + ibv.getClass().getName());
		}
	}

	public static Operator negateRelOp(final Operator relOp) {
		switch (relOp) {
		case COMPEQ:
			return Operator.COMPNEQ;
		case COMPNEQ:
			return Operator.COMPEQ;
		case COMPLEQ:
			return Operator.COMPGT;
		case COMPGT:
			return Operator.COMPLEQ;
		case COMPLT:
			return Operator.COMPGEQ;
		case COMPGEQ:
			return Operator.COMPLT;
		default:
			throw new IllegalArgumentException("Not a negatable relational operator: " + relOp);
		}
	}

	public static BoogieIcfgContainer getBoogieIcfgContainer(final IIcfg<?> icfg) {
		if (icfg instanceof BoogieIcfgContainer) {
			return (BoogieIcfgContainer) icfg;
		}
		final BoogieIcfgContainer bplIcfg = BoogieIcfgContainer.getAnnotation(icfg);
		if (bplIcfg != null) {
			return bplIcfg;
		}
		throw new IllegalArgumentException("Cannot extract BoogieIcfgContainer from IICFG");
	}

	public static <STATE extends IAbstractState<STATE>> STATE synchronizeVariables(final STATE template,
			final STATE toSynchronize) {
		if (toSynchronize == null) {
			return null;
		}
		if (template == null) {
			return toSynchronize;
		}
		final STATE rtr = synchronizeVariables(toSynchronize, template.getVariables());
		assert !toSynchronize.isBottom() || rtr.isBottom() : "Bottom is lost";
		return rtr;
	}

	public static <STATE extends IAbstractState<STATE>> Set<STATE> synchronizeVariables(final Set<STATE> states) {
		if (states == null) {
			return null;
		}
		if (states.size() < 2) {
			return states;
		}
		final Set<IProgramVarOrConst> allVars =
				states.stream().flatMap(a -> a.getVariables().stream()).collect(Collectors.toSet());
		return states.stream().map(a -> synchronizeVariables(a, allVars)).collect(Collectors.toSet());
	}

	public static <STATE extends IAbstractState<STATE>> STATE synchronizeVariables(final STATE state,
			final Set<IProgramVarOrConst> shouldVars) {

		final Set<IProgramVarOrConst> definedVariables = state.getVariables();

		final Set<IProgramVarOrConst> toRemove = DataStructureUtils.difference(definedVariables, shouldVars);
		final Set<IProgramVarOrConst> toAdd = DataStructureUtils.difference(shouldVars, definedVariables);

		if (toRemove.isEmpty() && toAdd.isEmpty()) {
			return state;
		}

		final STATE rtr;
		if (toRemove.isEmpty()) {
			rtr = state.addVariables(toAdd);
		} else if (toAdd.isEmpty()) {
			rtr = state.removeVariables(toRemove);
		} else {
			rtr = state.removeVariables(toRemove).addVariables(toAdd);
		}
		assert !state.isBottom() || rtr.isBottom() : "Bottom lost during synchronization";
		return rtr;
	}

	/**
	 * Accounts for found problems when passing values by string directly to BigDecimal, in order to avoid
	 * NumberFormatExceptions.
	 *
	 * @param val
	 *            The value as string.
	 * @return A new {@link BigDecimal} object that contains the given value. It is also possible that an exception is
	 *         thrown when the object is created if the given value is invalid or not handled.
	 */
	public static BigDecimal sanitizeBigDecimalValue(final String val) {
		if (val.contains("/")) {
			final String[] twoParts = val.split("/");
			if (twoParts.length != 2) {
				throw new NumberFormatException("Not a valid division value: " + val);
			}
			final BigDecimal one = new BigDecimal(twoParts[0]);
			final BigDecimal two = new BigDecimal(twoParts[1]);
			return one.divide(two);
		}
		return new BigDecimal(val);
	}

}
