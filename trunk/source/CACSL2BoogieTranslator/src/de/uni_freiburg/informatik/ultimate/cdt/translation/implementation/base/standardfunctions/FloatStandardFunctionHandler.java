package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CExpressionTranslator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationResultReporter;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.DataRaceChecker;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.FloatFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class FloatStandardFunctionHandler extends StandardFunctionHandler2 {
	//@formatter:off
	private final static String[] SUPPORTED_FLOAT_OPERATIONS = {
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

	private final static String[] UNSUPPORTED_FLOAT_OPERATIONS = {
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
		// https://en.cppreference.com/w/c/numeric/math/sin
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("sin", CPrimitives.DOUBLE);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("sinf", CPrimitives.FLOAT);
		OVERAPPROXIMATED_UNARY_FUNCTIONS.put("sinl", CPrimitives.LONGDOUBLE);

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

	public FloatStandardFunctionHandler(final ILogger logger, final Map<String, IASTNode> functionTable,
			final AuxVarInfoBuilder auxVarInfoBuilder, final INameHandler nameHandler,
			final ExpressionTranslation expressionTranslation, final MemoryHandler memoryHandler,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final ProcedureManager procedureManager,
			final CTranslationResultReporter reporter, final TypeSizes typeSizes, final FlatSymbolTable symboltable,
			final TranslationSettings settings, final ExpressionResultTransformer expressionResultTransformer,
			final LocationFactory locationFactory, final ITypeHandler typeHandler,
			final CExpressionTranslator cEpressionTranslator, final DataRaceChecker dataRaceChecker) {
		super(logger, functionTable, auxVarInfoBuilder, nameHandler, expressionTranslation, memoryHandler,
				typeSizeAndOffsetComputer, procedureManager, reporter, typeSizes, symboltable, settings,
				expressionResultTransformer, locationFactory, typeHandler, cEpressionTranslator, dataRaceChecker);
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();
		for (final var overapprox : OVERAPPROXIMATED_UNARY_FUNCTIONS.entrySet()) {
			result.add(new FunctionModel(overapprox.getKey(), (main, node, loc, name) -> handleByOverapproximation(main,
					node, loc, name, 1, new CPrimitive(overapprox.getValue()))));
		}

		// TODO: Move function with handleByOverapproximation to OVERAPPROXIMATED_UNARY_FUNCTIONS if possible
		// TODO: Group functions with this::handleUnaryFloatFunction in List
		// TODO: Group functions with this::handleBinaryFloatFunction in List

		/** various float builtins **/
		result.add(new FunctionModel("nan", (main, node, loc, name) -> handleNaNOrInfinity(loc, name)));
		result.add(new FunctionModel("nanf", (main, node, loc, name) -> handleNaNOrInfinity(loc, name)));
		result.add(new FunctionModel("nanl", (main, node, loc, name) -> handleNaNOrInfinity(loc, name)));
		result.add(new FunctionModel("__builtin_nan", (main, node, loc, name) -> handleNaNOrInfinity(loc, "nan")));
		result.add(new FunctionModel("__builtin_nanf", (main, node, loc, name) -> handleNaNOrInfinity(loc, "nanf")));
		result.add(new FunctionModel("__builtin_nanl", (main, node, loc, name) -> handleNaNOrInfinity(loc, "nanl")));
		result.add(new FunctionModel("__builtin_inff", (main, node, loc, name) -> handleNaNOrInfinity(loc, "inff")));
		result.add(new FunctionModel("__builtin_huge_val", (main, node, loc, name) -> handleNaNOrInfinity(loc, "inf")));
		result.add(
				new FunctionModel("__builtin_huge_valf", (main, node, loc, name) -> handleNaNOrInfinity(loc, "inff")));
		result.add(new FunctionModel("__builtin_isgreater",
				(main, node, loc, name) -> handleFloatBuiltinBinaryComparison(main, node, loc, name,
						IASTBinaryExpression.op_greaterThan)));
		result.add(new FunctionModel("__builtin_isgreaterequal",
				(main, node, loc, name) -> handleFloatBuiltinBinaryComparison(main, node, loc, name,
						IASTBinaryExpression.op_greaterEqual)));
		result.add(new FunctionModel("__builtin_isless", (main, node, loc,
				name) -> handleFloatBuiltinBinaryComparison(main, node, loc, name, IASTBinaryExpression.op_lessThan)));
		result.add(new FunctionModel("__builtin_islessequal", (main, node, loc,
				name) -> handleFloatBuiltinBinaryComparison(main, node, loc, name, IASTBinaryExpression.op_lessEqual)));
		result.add(new FunctionModel("__builtin_isunordered", this::handleFloatBuiltinIsUnordered));
		result.add(new FunctionModel("__builtin_islessgreater", this::handleFloatBuiltinIsLessGreater));
		result.add(new FunctionModel("__builtin_constant_p", (main, node, loc, name) -> handleByOverapproximation(main,
				node, loc, name, 1, new CPrimitive(CPrimitives.BOOL))));
		result.add(new FunctionModel("__builtin_isinf_sign", (main, node, loc, name) -> handleByOverapproximation(main,
				node, loc, name, 1, new CPrimitive(CPrimitives.INT))));
		result.add(new FunctionModel("__builtin_isnan",
				(main, node, loc, name) -> handleUnaryFloatFunction(main, node, loc, "isnan")));

		/** math.h float functions **/
		// see 7.12.3.1 or http://en.cppreference.com/w/c/numeric/math/fpclassify
		result.add(new FunctionModel("fpclassify", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("__fpclassify", this::handleUnaryFloatFunction)); // ??
		result.add(new FunctionModel("__fpclassifyf", this::handleUnaryFloatFunction)); // ??
		result.add(new FunctionModel("__fpclassifyl", this::handleUnaryFloatFunction)); // ??

		// see 7.12.3.2 or http://en.cppreference.com/w/c/numeric/math/isfinite
		result.add(new FunctionModel("isfinite", this::handleUnaryFloatFunction));

		// see https://linux.die.net/man/3/finite (! NOT PART OF ANSI-C)
		result.add(new FunctionModel("finite", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("__finite", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("finitef", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("__finitef", this::handleUnaryFloatFunction)); // ??
		result.add(new FunctionModel("finitel", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("__finitel", this::handleUnaryFloatFunction)); // ??

		// see 7.12.3.3 or http://en.cppreference.com/w/c/numeric/math/isinf
		result.add(new FunctionModel("isinf", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("__isinf", this::handleUnaryFloatFunction)); // ??
		// see https://linux.die.net/man/3/finite (! NOT PART OF ANSI-C)
		result.add(new FunctionModel("isinff", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("__isinff", this::handleUnaryFloatFunction)); // ??
		result.add(new FunctionModel("isinfl", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("__isinfl", this::handleUnaryFloatFunction)); // ??

		// see 7.12.3.4 or http://en.cppreference.com/w/c/numeric/math/isnan
		result.add(new FunctionModel("isnan", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("__isnan", this::handleUnaryFloatFunction)); // ??
		// see https://linux.die.net/man/3/finite (! NOT PART OF ANSI-C)
		result.add(new FunctionModel("isnanf", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("isnanl", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("__isnanf", this::handleUnaryFloatFunction)); // ??
		result.add(new FunctionModel("__isnanl", this::handleUnaryFloatFunction)); // ??

		// see 7.12.3.5 or http://en.cppreference.com/w/c/numeric/math/isnormal
		result.add(new FunctionModel("isnormal", this::handleUnaryFloatFunction));

		// see 7.12.7.5 or http://en.cppreference.com/w/c/numeric/math/sqrt
		result.add(new FunctionModel("sqrt", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("sqrtf", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("sqrtl", this::handleUnaryFloatFunction));

		// see 7.12.7.2 or http://en.cppreference.com/w/c/numeric/math/fabs
		result.add(new FunctionModel("fabs", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("fabsf", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("fabsl", this::handleUnaryFloatFunction));

		// see 7.12.9.8 or http://en.cppreference.com/w/c/numeric/math/trunc
		result.add(new FunctionModel("trunc", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("truncf", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("truncl", this::handleUnaryFloatFunction));

		// see 7.12.9.6 or http://en.cppreference.com/w/c/numeric/math/round
		result.add(new FunctionModel("round", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("roundf", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("roundl", this::handleUnaryFloatFunction));
		// see 7.12.9.7 or http://en.cppreference.com/w/c/numeric/math/round
		result.add(new FunctionModel("lround", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("lroundf", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("lroundl", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("llround", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("llroundf", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("llroundl", this::handleUnaryFloatFunction));

		// see 7.12.9.2 or http://en.cppreference.com/w/c/numeric/math/floor
		result.add(new FunctionModel("floor", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("floorf", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("floorl", this::handleUnaryFloatFunction));

		// see 7.12.9.1 or http://en.cppreference.com/w/c/numeric/math/ceil
		result.add(new FunctionModel("ceil", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("ceilf", this::handleUnaryFloatFunction));
		result.add(new FunctionModel("ceill", this::handleUnaryFloatFunction));

		// see 7.12.12.2 or http://en.cppreference.com/w/c/numeric/math/fmax
		// NaN arguments are treated as missing data: if one argument is a NaN and the
		// other numeric, then the
		// fmin/fmax functions choose the numeric value.
		result.add(new FunctionModel("fmax", this::handleBinaryFloatFunction));
		result.add(new FunctionModel("fmaxf", this::handleBinaryFloatFunction));
		result.add(new FunctionModel("fmaxl", this::handleBinaryFloatFunction));

		// see 7.12.12.3 or http://en.cppreference.com/w/c/numeric/math/fmin
		result.add(new FunctionModel("fmin", this::handleBinaryFloatFunction));
		result.add(new FunctionModel("fminf", this::handleBinaryFloatFunction));
		result.add(new FunctionModel("fminl", this::handleBinaryFloatFunction));

		// see 7.12.10.2 or http://en.cppreference.com/w/c/numeric/math/remainder
		result.add(new FunctionModel("remainder", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("remainderf", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("remainderl", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPrimitive(CPrimitives.LONGDOUBLE))));

		// see 7.12.10.1 or http://en.cppreference.com/w/c/numeric/math/fmod
		result.add(new FunctionModel("fmod", this::handleBinaryFloatFunction));
		result.add(new FunctionModel("fmodf", this::handleBinaryFloatFunction));
		result.add(new FunctionModel("fmodl", this::handleBinaryFloatFunction));

		// see 7.12.11.1 or http://en.cppreference.com/w/c/numeric/math/copysign
		result.add(new FunctionModel("copysign", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("copysignf", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("copysignl", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPrimitive(CPrimitives.LONGDOUBLE))));

		// see 7.12.12.1 or https://en.cppreference.com/w/c/numeric/math/fdim
		result.add(new FunctionModel("fdim", this::handleBinaryFloatFunction));
		result.add(new FunctionModel("fdimf", this::handleBinaryFloatFunction));
		result.add(new FunctionModel("fdiml", this::handleBinaryFloatFunction));

		// TODO: Check in SUPPORTED_FLOAT_FUNCTIONS
		return result;
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return Arrays.asList(UNSUPPORTED_FLOAT_OPERATIONS);
	}

	private Result handleNaNOrInfinity(final ILocation loc, final String methodName) {
		return mExpressionTranslation.createNanOrInfinity(loc, methodName);
	}

	private Result handleUnaryFloatFunction(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final FloatFunction floatFunction = FloatFunction.decode(name);
		final ExpressionResult arg = handleFloatArguments(main, node, loc, name, 1, floatFunction).get(0);
		final RValue rvalue =
				mExpressionTranslation.constructOtherUnaryFloatOperation(loc, floatFunction, (RValue) arg.getLrValue());
		return new ExpressionResultBuilder().addAllExceptLrValue(arg).setLrValue(rvalue).build();
	}

	private Result handleBinaryFloatFunction(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final FloatFunction floatFunction = FloatFunction.decode(name);
		final List<ExpressionResult> args = handleFloatArguments(main, node, loc, name, 2, floatFunction);
		final RValue rvalue = mExpressionTranslation.constructOtherBinaryFloatOperation(loc, floatFunction,
				(RValue) args.get(0).getLrValue(), (RValue) args.get(1).getLrValue());
		return new ExpressionResultBuilder().addAllExceptLrValue(args).setLrValue(rvalue).build();
	}

	private List<ExpressionResult> handleFloatArguments(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final int numberOfArgs, final FloatFunction floatFunction) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, numberOfArgs, name, arguments);
		if (floatFunction == null) {
			throw new IllegalArgumentException(
					"Ultimate declared float handling for " + name + ", but is not known float function");
		}
		final List<ExpressionResult> rtr = new ArrayList<>();
		for (final IASTInitializerClause argument : arguments) {
			final ExpressionResult decayedArgument =
					mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, argument);
			final ExpressionResult convertedArgument =
					mExprResultTransformer.convertIfNecessary(loc, decayedArgument, floatFunction.getType());
			rtr.add(convertedArgument);
		}

		final CPrimitive typeDeterminedByName = floatFunction.getType();
		if (typeDeterminedByName != null) {
			final List<ExpressionResult> newRtr = new ArrayList<>();
			for (final ExpressionResult arg : rtr) {
				newRtr.add(mExprResultTransformer.convertIfNecessary(loc, arg, typeDeterminedByName));
			}
			return newRtr;
		}
		return rtr;
	}

	private Result handleFloatBuiltinBinaryComparison(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final int op) {
		/*
		 * Handle the following float comparisons
		 *
		 * http://en.cppreference.com/w/c/numeric/math/isless
		 *
		 * http://en.cppreference.com/w/c/numeric/math/islessequal
		 *
		 * http://en.cppreference.com/w/c/numeric/math/isgreater
		 *
		 * http://en.cppreference.com/w/c/numeric/math/isgreaterequal
		 *
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);

		final ExpressionResult rl =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult rr =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);

		// Note: this works because SMTLIB already ensures that all comparisons return false if one of the arguments is
		// NaN

		return mCEpressionTranslator.handleRelationalOperators(loc, op, rl, rr);
	}

	/**
	 * Handle the following macro. <code>int isunordered (real-floating x, real-floating y)</code>
	 *
	 * This macro determines whether its arguments are unordered. It is 1 if x or y are NaN, and 0 otherwise.
	 *
	 * According to 7.12.14.6 of C11 the isunordered macro returns 1 if its arguments are unordered and 0 otherwise. The
	 * meaning of "unordered" is defined in 7.12.14. Two floating point values are unordered if at least one of the two
	 * is a NaN value.
	 *
	 * See also http://en.cppreference.com/w/c/numeric/math/isunordered
	 *
	 */
	private Result handleFloatBuiltinIsUnordered(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);

		final ExpressionResult leftRvaluedResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult rightRvaluedResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);
		final ExpressionResult nanLResult =
				mExpressionTranslation.createNan(loc, (CPrimitive) leftRvaluedResult.getLrValue().getCType());
		final ExpressionResult nanRResult =
				mExpressionTranslation.createNan(loc, (CPrimitive) rightRvaluedResult.getLrValue().getCType());
		final Expression leftExpr = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ,
				leftRvaluedResult.getLrValue().getValue(), nanLResult.getLrValue().getValue());
		final Expression rightExpr = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ,
				rightRvaluedResult.getLrValue().getValue(), nanRResult.getLrValue().getValue());
		final Expression expr = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftExpr, rightExpr);
		final LRValue lrVal = new RValue(expr, new CPrimitive(CPrimitives.INT), true);
		final ExpressionResult rtr = new ExpressionResultBuilder()
				.addAllExceptLrValue(leftRvaluedResult, rightRvaluedResult, nanLResult, nanRResult).setLrValue(lrVal)
				.build();
		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, rtr.getDeclarations(), rtr.getAuxVars());
		return rtr;
	}

	private Result handleFloatBuiltinIsLessGreater(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		/*
		 * http://en.cppreference.com/w/c/numeric/math/islessgreater
		 *
		 * int islessgreater (real-floating x, real-floating y)
		 *
		 * This macro determines whether the argument x is less or greater than y.
		 *
		 * It is equivalent to (x) < (y) || (x) > (y) (although it only evaluates x and y once), but no exception is
		 * raised if x or y are NaN.
		 *
		 * This macro is not equivalent to x != y, because that expression is true if x or y are NaN.
		 *
		 * Note: I did not find any reference as to how often x and y are evaluated; it seems this can actually evaluate
		 * x and y twice.
		 */

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);

		ExpressionResult leftOp =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		ExpressionResult rightOp =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);
		final Pair<ExpressionResult, ExpressionResult> newOps =
				mExprResultTransformer.usualArithmeticConversions(loc, leftOp, rightOp);
		leftOp = newOps.getFirst();
		rightOp = newOps.getSecond();

		final ExpressionResult lessThan =
				mCEpressionTranslator.handleRelationalOperators(loc, IASTBinaryExpression.op_lessThan, leftOp, rightOp);
		final ExpressionResult greaterThan = mCEpressionTranslator.handleRelationalOperators(loc,
				IASTBinaryExpression.op_greaterThan, leftOp, rightOp);

		final Expression expr = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
				lessThan.getLrValue().getValue(), greaterThan.getLrValue().getValue());
		final LRValue lrVal = new RValue(expr, new CPrimitive(CPrimitives.INT), true);
		final ExpressionResult rtr =
				new ExpressionResultBuilder().addAllExceptLrValue(lessThan, greaterThan).setLrValue(lrVal).build();
		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, rtr.getDeclarations(), rtr.getAuxVars());
		return rtr;
	}
}
