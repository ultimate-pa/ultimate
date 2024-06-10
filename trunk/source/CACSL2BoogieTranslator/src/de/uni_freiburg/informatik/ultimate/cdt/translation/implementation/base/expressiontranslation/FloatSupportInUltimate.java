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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;

/**
 * Auxiliary file that contains information about float operations of env.h and math.h support in ultimate.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class FloatSupportInUltimate {
	//@formatter:off

	private final static String[] SUPPORTED_FLOAT_OPERATIONS_ARRAY = new String[] {
			"sqrt",
			"__isinf",
			"__finite",
			"isinf",
			"finite",
			"nan",
			"__isnan",
			"isnan",
			"__fpclassify",
			"sqrtf",
			"__isinff",
			"isinff",
			"__finitef",
			"finitef",
			"nanf",
			"__isnanf",
			"isnanf",
			"__fpclassifyf",
			"sqrtl",
			"__isinfl",
			"__finitel",
			"isinfl",
			"finitel",
			"nanl",
			"__isnanl",
			"isnanl",
			"__fpclassifyl",
			"fabs",
			"fabsf",
			"fabsl",
			"fmax",
			"fmin",
			"fmaxf",
			"fminf",
			"fmaxl",
			"fminl",
			"trunc",
			"truncf",
			"truncl",
			"round",
			"lround",
			"llround",
			"roundf",
			"lroundf",
			"llroundf",
			"roundl",
			"lroundl",
			"llroundl",
			"floor",
			"floorf",
			"floorl",
			"ceil",
			"ceilf",
			"ceill",
			"remainder",
			"remainderf",
			"remainderl",
			"fmod",
			"fmodf",
			"fmodl",
			"copysign",
			"copysignf",
			"copysignl",
			"fdim",
			"fdimf",
			"fdiml",
			// math.h macros (incomplete)
			"fpclassify",
			"isnormal",

			// from fenv.h
			"fegetround",
			"fesetround",
	};

	private final static String[] UNSUPPORTED_FLOAT_OPERATIONS_ARRAY = new String[] {
			// from math.h
			"frexp",
			"ldexp",
			"pow",
			"hypot",
			"cbrt",
			"drem",
			"significand",
			"j0",
			"j1",
			"jn",
			"y0",
			"y1",
			"yn",
			"erfc",
			"lgamma",
			"tgamma",
			"gamma",
			"lgamma_r",
			"nextafter",
			"nexttoward",
			"scalbn",
			"ilogb",
			"scalbln",
			"remquo",
			"lrint",
			"llrint",
			"fma",
			"scalb",
			"frexpf",
			"ldexpf",
			"powf",
			"hypotf",
			"cbrtf",
			"dremf",
			"significandf",
			"j0f",
			"j1f",
			"jnf",
			"y0f",
			"y1f",
			"ynf",
			"erfcf",
			"lgammaf",
			"tgammaf",
			"gammaf",
			"lgammaf_r",
			"nextafterf",
			"nexttowardf",
			"scalbnf",
			"ilogbf",
			"scalblnf",
			"remquof",
			"lrintf",
			"llrintf",
			"fmaf",
			"scalbf",
			"frexpl",
			"ldexpl",
			"powl",
			"hypotl",
			"cbrtl",
			"dreml",
			"significandl",
			"j0l",
			"j1l",
			"jnl",
			"y0l",
			"y1l",
			"ynl",
			"erfcl",
			"lgammal",
			"tgammal",
			"gammal",
			"lgammal_r",
			"nextafterl",
			"nexttowardl",
			"scalbnl",
			"ilogbl",
			"scalblnl",
			"remquol",
			"lrintl",
			"llrintl",
			"fmal",
			"scalbl",
			"signgam;",
			"modf",
			"modff",
			"modfl",

			// from fenv.h
			"feclearexcept",
			"fegetexceptflag",
			"feraiseexcept",
			"fesetexceptflag",
			"fetestexcept",
			"fegetenv",
			"feholdexcept",
			"fesetenv",
			"feupdateenv",
	};
	//@formatter:on

	private final static Map<String, CPrimitives> OVERAPPROXIMATED_UNARY_FUNCTIONS = new HashMap<>();
	static {
		// https://en.cppreference.com/w/c/numeric/math/exp
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("exp", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("expf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("expl", CPrimitives.LONGDOUBLE);

		// https://en.cppreference.com/w/c/numeric/math/expm1
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("expm1", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("expm1f", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("expm1l", CPrimitives.LONGDOUBLE);

		// https://en.cppreference.com/w/c/numeric/math/tanh
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("tanh", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("tanhf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("tanhl", CPrimitives.LONGDOUBLE);

		// https://en.cppreference.com/w/c/numeric/math/erf
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("erf", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("erff", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("erfl", CPrimitives.LONGDOUBLE);

		// https://en.cppreference.com/w/c/numeric/math/log
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("log", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("logf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("logl", CPrimitives.LONGDOUBLE);

		// https://en.cppreference.com/w/c/numeric/math/cos
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("cos", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("cosf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("cosl", CPrimitives.LONGDOUBLE);

		// https://en.cppreference.com/w/c/numeric/math/log1p
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("log1p", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("log1pf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("log1pl", CPrimitives.LONGDOUBLE);

		// https://en.cppreference.com/w/c/numeric/math/rint
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("rint", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("rintf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("rintl", CPrimitives.LONGDOUBLE);

		// https://en.cppreference.com/w/c/numeric/math/atanh
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("atanh", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("atanhf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("atanhl", CPrimitives.LONGDOUBLE);

		// https://en.cppreference.com/w/c/numeric/math/asin
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("asin", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("asinf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("asinl", CPrimitives.LONGDOUBLE);

		// https://en.cppreference.com/w/c/numeric/math/acos
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("acos", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("acosf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("acosl", CPrimitives.LONGDOUBLE);

		// https://en.cppreference.com/w/c/numeric/math/nearbyint
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("nearbyint", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("nearbyintf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("nearbyintl", CPrimitives.LONGDOUBLE);

		// http://en.cppreference.com/w/c/numeric/math/signbit
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("signbit", CPrimitives.INT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("__signbit", CPrimitives.INT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("__signbitl", CPrimitives.INT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("__signbitf", CPrimitives.INT);

		// http://en.cppreference.com/w/c/numeric/math/atan
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("atan", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("atanf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("atanl", CPrimitives.LONGDOUBLE);

		// http://en.cppreference.com/w/c/numeric/math/atan2
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("atan2", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("atan2f", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("atan2l", CPrimitives.LONGDOUBLE);

		// http://en.cppreference.com/w/c/numeric/math/tan
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("tan", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("tanf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("tanl", CPrimitives.LONGDOUBLE);

		// http://en.cppreference.com/w/c/numeric/math/cosh
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("cosh", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("coshf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("coshl", CPrimitives.LONGDOUBLE);

		// http://en.cppreference.com/w/c/numeric/math/sinh
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("sinh", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("sinhf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("sinhl", CPrimitives.LONGDOUBLE);

		// http://en.cppreference.com/w/c/numeric/math/acosh
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("acosh", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("acoshf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("acoshl", CPrimitives.LONGDOUBLE);

		// http://en.cppreference.com/w/c/numeric/math/asinh
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("asinh", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("asinhf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("asinhl", CPrimitives.LONGDOUBLE);

		// http://en.cppreference.com/w/c/numeric/math/log10
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("log10", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("log10f", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("log10l", CPrimitives.LONGDOUBLE);

		// http://en.cppreference.com/w/c/numeric/math/logb
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("logb", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("logbf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("logbl", CPrimitives.LONGDOUBLE);

		// http://en.cppreference.com/w/c/numeric/math/exp2
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("exp2", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("exp2f", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("exp2l", CPrimitives.LONGDOUBLE);

		// http://en.cppreference.com/w/c/numeric/math/log2
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("log2", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("log2f", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("log2l", CPrimitives.LONGDOUBLE);
	}

	private final static Set<String> SUPPORTED_FLOAT_OPERATIONS =
			new HashSet<>(Arrays.asList(SUPPORTED_FLOAT_OPERATIONS_ARRAY));

	private final static Set<String> UNSUPPORTED_FLOAT_OPERATIONS =
			new HashSet<>(Arrays.asList(UNSUPPORTED_FLOAT_OPERATIONS_ARRAY));

	public static Set<String> getUnsupportedFloatOperations() {
		return UNSUPPORTED_FLOAT_OPERATIONS;
	}

	public static Set<String> getSupportedFloatOperations() {
		return SUPPORTED_FLOAT_OPERATIONS;
	}

	public static Map<String, CPrimitives> getOverapproximatedUnaryFunctions() {
		return OVERAPPROXIMATED_UNARY_FUNCTIONS;
	}
}