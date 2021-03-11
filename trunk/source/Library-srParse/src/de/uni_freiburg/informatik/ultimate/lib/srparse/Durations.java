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

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern.VariableCategory;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class Durations {

	private final Map<String, Rational> mKnownNumericConstants;
	private final Set<Rational> mKnownNumericValues;
	private final Consumer<String> mFunAddError;

	private int mKnownValues;
	private Rational mEpsilon;

	public Durations(final Consumer<String> funAddError) {
		mKnownNumericConstants = new LinkedHashMap<>();
		mKnownNumericValues = new HashSet<>();
		mFunAddError = funAddError;
	}

	public Durations() {
		this(a -> {
			// dummy consumer
		});
	}

	public void addInitPattern(final InitializationPattern init) {
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
		mKnownNumericValues.addAll(p.getDurations());

	}

	private Rational tryParse(final InitializationPattern init, final Expression expr) {
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
		if (mEpsilon == null || mKnownNumericValues.size() != mKnownValues) {
			mKnownValues = mKnownNumericValues.size();
			if (mKnownValues == 0) {
				mEpsilon = Rational.ZERO;
			} else {
				mEpsilon = SmtUtils.gcd(mKnownNumericValues).div(Rational.TWO);
			}
		}
		return mEpsilon;
	}

}
