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
import java.util.HashSet;
import java.util.Set;

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
			"signbit",
			"__isinf",
			"__finite",
			"isinf",
			"finite",
			"nan",
			"__isnan",
			"isnan",
			"__fpclassify",
			"__signbit",
			"sqrtf",
			"__isinff",
			"isinff",
			"__finitef",
			"finitef",
			"nanf",
			"__isnanf",
			"isnanf",
			"__fpclassifyf",
			"__signbitf",
			"sqrtl",
			"__isinfl",
			"__finitel",
			"isinfl",
			"finitel",
			"nanl",
			"__isnanl",
			"isnanl",
			"__fpclassifyl",
			"__signbitl",
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
			"sin",
			"sinf",
			"sinl",
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
			"isnormal"
	};

	private final static String[] UNSUPPORTED_FLOAT_OPERATIONS_ARRAY = new String[] {
			// from math.h
			"acos",
			"asin",
			"atan",
			"atan2",
			"cos",
			"tan",
			"cosh",
			"sinh",
			"tanh",
			"acosh",
			"asinh",
			"atanh",
			"exp",
			"frexp",
			"ldexp",
			"log",
			"log10",
			"modf",
			"expm1",
			"log1p",
			"logb",
			"exp2",
			"log2",
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
			"erf",
			"erfc",
			"lgamma",
			"tgamma",
			"gamma",
			"lgamma_r",
			"rint",
			"nextafter",
			"nexttoward",
			"scalbn",
			"ilogb",
			"scalbln",
			"nearbyint",
			"remquo",
			"lrint",
			"llrint",
			"fma",
			"scalb",
			"acosf",
			"asinf",
			"atanf",
			"atan2f",
			"cosf",
			"tanf",
			"coshf",
			"sinhf",
			"tanhf",
			"acoshf",
			"asinhf",
			"atanhf",
			"expf",
			"frexpf",
			"ldexpf",
			"logf",
			"log10f",
			"modff",
			"expm1f",
			"log1pf",
			"logbf",
			"exp2f",
			"log2f",
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
			"erff",
			"erfcf",
			"lgammaf",
			"tgammaf",
			"gammaf",
			"lgammaf_r",
			"rintf",
			"nextafterf",
			"nexttowardf",
			"scalbnf",
			"ilogbf",
			"scalblnf",
			"nearbyintf",
			"remquof",
			"lrintf",
			"llrintf",
			"fmaf",
			"scalbf",
			"acosl",
			"asinl",
			"atanl",
			"atan2l",
			"cosl",
			"tanl",
			"coshl",
			"sinhl",
			"tanhl",
			"acoshl",
			"asinhl",
			"atanhl",
			"expl",
			"frexpl",
			"ldexpl",
			"logl",
			"log10l",
			"modfl",
			"expm1l",
			"log1pl",
			"logbl",
			"exp2l",
			"log2l",
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
			"erfl",
			"erfcl",
			"lgammal",
			"tgammal",
			"gammal",
			"lgammal_r",
			"rintl",
			"nextafterl",
			"nexttowardl",
			"scalbnl",
			"ilogbl",
			"scalblnl",
			"nearbyintl",
			"remquol",
			"lrintl",
			"llrintl",
			"fmal",
			"scalbl",
			"signgam;",

			// from fenv.h
			"feclearexcept",
			"fegetexceptflag",
			"feraiseexcept",
			"fesetexceptflag",
			"fetestexcept",
			"fegetround",
			"fesetround",
			"fegetenv",
			"feholdexcept",
			"fesetenv",
			"feupdateenv",
	};
	//@formatter:on

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

}
