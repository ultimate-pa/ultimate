/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.srparse;

import java.math.BigInteger;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern.VariableCategory;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.util.Lazy;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class Durations {

	private final Map<String, Rational> mKnownNumericConstants;
	private final Set<Rational> mKnownNumericValues;
	private final Consumer<String> mFunAddError;

	private final DirtyLazy<Rational> mEpsilon;
	private final DirtyLazy<Rational> mScalingFactor;

	public Durations(final Consumer<String> funAddError) {
		mKnownNumericConstants = new LinkedHashMap<>();
		mKnownNumericValues = new HashSet<>();
		mFunAddError = funAddError;
		mEpsilon = new DirtyLazy<>(this::computeEpsilonInternal);
		mScalingFactor = new DirtyLazy<>(this::computeScalingFactorInternal);
	}

	public Durations() {
		this(a -> {
			// dummy consumer
		});
	}

	private Rational computeEpsilonInternal() {
		return mKnownNumericValues.isEmpty() ? Rational.ZERO : SmtUtils.gcd(mKnownNumericValues).div(Rational.TWO);
	}

	private Rational computeScalingFactorInternal() {
		if (mKnownNumericValues.isEmpty()) {
			return Rational.ONE;
		}
		final List<Rational> nonIntegral =
				mKnownNumericValues.stream().filter(a -> !a.isIntegral()).collect(Collectors.toList());
		if (nonIntegral.isEmpty()) {
			return Rational.ONE;
		}
		if (nonIntegral.size() == 1) {
			return Rational.valueOf(nonIntegral.get(0).denominator().abs(), BigInteger.ONE);
		}
		final Iterator<BigInteger> iter = nonIntegral.stream().map(a -> a.denominator().abs()).iterator();
		final BigInteger a = iter.next();
		final BigInteger b = iter.next();
		BigInteger gcd = Rational.gcd(a, b);
		BigInteger lcm = a.multiply(b).abs().divide(gcd);
		while (iter.hasNext()) {
			final BigInteger next = iter.next();
			gcd = Rational.gcd(lcm, next);
			lcm = lcm.multiply(next).abs().divide(gcd);
		}
		return Rational.valueOf(lcm, BigInteger.ONE);
	}

	public void addInitPattern(final DeclarationPattern init) {
		if (init.getCategory() != VariableCategory.CONST) {
			return;
		}
		final BoogiePrimitiveType type = BoogiePrimitiveType.toPrimitiveType(init.getType());
		if (type != BoogieType.TYPE_INT && type != BoogieType.TYPE_REAL) {
			return;
		}
		final Expression expr = init.getExpression();
		final Rational val = tryParse(init, expr);
		if (val == null) {
			return;
		}
		mKnownNumericConstants.put(init.getId(), val);
	}

	public void addNonInitPattern(final PatternType<?> p) {
		if (mKnownNumericValues.addAll(p.getDurations())) {
			mEpsilon.markDirty();
			mScalingFactor.markDirty();
		}

	}

	private Rational tryParse(final DeclarationPattern init, final Expression expr) {
		final Optional<Rational> val = LiteralUtils.toRational(expr);
		if (val.isEmpty()) {
			error(init, "Cannot convert expression " + BoogiePrettyPrinter.print(expr) + " to Rational");
			return null;
		}
		return val.get();
	}

	private void error(final PatternType<?> pattern, final String message) {
		final String t = String.format("%s: %s", pattern.getId(), message);
		mFunAddError.accept(t);
	}

	public Rational getConstantValue(final String name) {
		return mKnownNumericConstants.get(name);
	}

	public Set<String> getConstNames() {
		return mKnownNumericConstants.keySet();
	}

	public Rational computeEpsilon() {
		return mEpsilon.get();
	}

	public Rational computeScalingFactor() {
		return mScalingFactor.get();
	}

	public Durations merge(final Collection<Durations> durations) {
		final Consumer<String> funAddError =
				durations.stream().map(d -> d.mFunAddError).reduce(mFunAddError, Consumer::andThen);
		final Durations rtr = new Durations(funAddError);

		rtr.mKnownNumericConstants.putAll(mKnownNumericConstants);
		rtr.mKnownNumericValues.addAll(mKnownNumericValues);

		for (final Durations d : durations) {
			rtr.mKnownNumericConstants.putAll(d.mKnownNumericConstants);
			rtr.mKnownNumericValues.addAll(d.mKnownNumericValues);
		}
		return rtr;
	}

	private static final class DirtyLazy<V> {
		private Lazy<V> mValue;
		private final Supplier<V> mFun;

		public DirtyLazy(final Supplier<V> fun) {
			mValue = new Lazy<>(fun);
			mFun = fun;
		}

		public V get() {
			return mValue.get();
		}

		public void markDirty() {
			mValue = new Lazy<>(mFun);
		}

	}
}
