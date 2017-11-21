/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;

/**
 * Auxiliary class for decomposing and representing C float functions.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class FloatFunction {

	/**
	 * Prefix that floating point functions get after preprocessing with gcc.
	 */
	private static final String GCC_PREFIX = "__";

	private static final String[] FLOAT_FUNCTIONS = { "fpclassify", // see 7.12.3.1
			"isfinite", "finite", // see 7.12.3.2
			"isinf", // see 7.12.3.3
			"isnan", // see 7.12.3.4
			"isnormal", // see 7.12.3.5
			"signbit", // see 7.12.3.6
			"sqrt", "fabs", // see 7.12.7.2
	};

	private static final String[] TYPE_SUFFIXES = { "f", "d", "l" };

	private final String mPrefix;
	private final String mFunction;
	private final String mTypeSuffix;

	public FloatFunction(final String prefix, final String function, final String typeSuffix) {
		super();
		mPrefix = prefix;
		mFunction = function;
		mTypeSuffix = typeSuffix;
	}

	public String getPrefix() {
		return mPrefix;
	}

	public String getFunctionName() {
		return mFunction;
	}

	public String getTypeSuffix() {
		return mTypeSuffix;
	}

	public CPrimitive getType() {
		switch (mTypeSuffix) {
		case "":
			return null;
		case "f":
			return new CPrimitive(CPrimitives.FLOAT);
		case "d":
			return new CPrimitive(CPrimitives.DOUBLE);
		case "l":
			return new CPrimitive(CPrimitives.LONGDOUBLE);
		default:
			throw new AssertionError("unknown type suffix " + mTypeSuffix);
		}
	}

	public static FloatFunction decode(final String fullFunctionName) {
		final String withoutPrefix;
		final String prefix;
		if (fullFunctionName.startsWith(GCC_PREFIX)) {
			withoutPrefix = fullFunctionName.substring(2);
			prefix = GCC_PREFIX;
		} else {
			withoutPrefix = fullFunctionName;
			prefix = "";
		}
		final String function = returnFirstMatching(withoutPrefix);
		if (function == null) {
			return null;
		}
		final String typeSuffix;
		final String remaining = withoutPrefix.substring(function.length());
		if (remaining.isEmpty()) {
			typeSuffix = "";
		} else if (Arrays.asList(TYPE_SUFFIXES).contains(remaining)) {
			typeSuffix = remaining;
		} else {
			// some string remaining that we cannot decode
			return null;
		}
		return new FloatFunction(prefix, function, typeSuffix);
	}

	private static String returnFirstMatching(final String withoutPrefix) {
		for (final String floatFunction : FLOAT_FUNCTIONS) {
			if (withoutPrefix.startsWith(floatFunction)) {
				return floatFunction;
			}
		}
		return null;
	}

}
