package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CExpressionTranslator;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class FloatFunctionModelProvider extends FunctionModelProvider {
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

	private static final List<String> UNARY_FUNCTIONS = List.of(
			// see 7.12.3.1 or http://en.cppreference.com/w/c/numeric/math/fpclassify
			"fpclassify", "__fpclassify", "__fpclassifyf", "__fpclassifyl",

			// see 7.12.3.2 or http://en.cppreference.com/w/c/numeric/math/isfinite
			"isfinite",

			// see 7.12.3.3 or http://en.cppreference.com/w/c/numeric/math/isinf
			"isinf", "__isinf",

			// see 7.12.3.4 or http://en.cppreference.com/w/c/numeric/math/isnan
			"isnan", "__isnan",

			// see https://linux.die.net/man/3/finite (! NOT PART OF ANSI-C)
			"finite", "__finite", "finitef", "__finitef", "finitel", "__finitel",
			"isinff", "__isinff", "isinfl", "__isinfl",
			"isnanf", "isnanl", "__isnanf", "__isnanl",

			// see 7.12.3.5 or http://en.cppreference.com/w/c/numeric/math/isnormal
			"isnormal",

			// see 7.12.7.5 or http://en.cppreference.com/w/c/numeric/math/sqrt
			"sqrt", "sqrtf", "sqrtl",

			// see 7.12.7.2 or http://en.cppreference.com/w/c/numeric/math/fabs
			"fabs", "fabsf", "fabsl",

			// see 7.12.9.8 or http://en.cppreference.com/w/c/numeric/math/trunc
			"trunc", "truncf", "truncl",

			// see 7.12.9.6 or http://en.cppreference.com/w/c/numeric/math/round
			"round", "roundf", "roundl",

			// see 7.12.9.7 or http://en.cppreference.com/w/c/numeric/math/round
			"lround", "lroundf", "lroundl", "llround", "llroundf", "llroundl",

			// see 7.12.9.2 or http://en.cppreference.com/w/c/numeric/math/floor
			"floor", "floorf", "floorl",

			// see 7.12.9.1 or http://en.cppreference.com/w/c/numeric/math/ceil
			"ceil", "ceilf", "ceilr"
			);

	private static final List<String> BINARY_FUNCTIONS = List.of(
			// see 7.12.12.2 or http://en.cppreference.com/w/c/numeric/math/fmax
			// NaN arguments are treated as missing data: if one argument is a NaN and the
			// other numeric, then the
			// fmin/fmax functions choose the numeric value.
			"fmax", "fmaxf", "fmaxl",

			// see 7.12.12.3 or http://en.cppreference.com/w/c/numeric/math/fmin
			"fmin", "fminf", "fminl",

			// see 7.12.10.1 or http://en.cppreference.com/w/c/numeric/math/fmod
			"fmod", "fmodf", "fmodl",

			// see 7.12.12.1 or https://en.cppreference.com/w/c/numeric/math/fdim
			"fdim", "fdimf", "fdiml"
			);
	//@formatter:on

	public FloatFunctionModelProvider(final Map<String, IASTNode> functionTable,
			final AuxVarInfoBuilder auxVarInfoBuilder, final INameHandler nameHandler,
			final ExpressionTranslation expressionTranslation, final MemoryHandler memoryHandler,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final ProcedureManager procedureManager,
			final TypeSizes typeSizes, final TranslationSettings settings,
			final ExpressionResultTransformer expressionResultTransformer, final ITypeHandler typeHandler,
			final CExpressionTranslator cEpressionTranslator, final DataRaceChecker dataRaceChecker) {
		super(functionTable, auxVarInfoBuilder, nameHandler, expressionTranslation, memoryHandler,
				typeSizeAndOffsetComputer, procedureManager, typeSizes, settings, expressionResultTransformer,
				typeHandler, cEpressionTranslator, dataRaceChecker);
	}

	private static List<Pair<String, CPrimitives>> getOverapproximatedUnaryFunctions() {
		final List<Pair<String, CPrimitives>> result = new ArrayList<>();

		// https://en.cppreference.com/w/c/numeric/math/sin
		result.add(new Pair<>("sin", CPrimitives.DOUBLE));
		result.add(new Pair<>("sinf", CPrimitives.FLOAT));
		result.add(new Pair<>("sinl", CPrimitives.LONGDOUBLE));

		// https://en.cppreference.com/w/c/numeric/math/exp
		result.add(new Pair<>("exp", CPrimitives.DOUBLE));
		result.add(new Pair<>("expf", CPrimitives.FLOAT));
		result.add(new Pair<>("expl", CPrimitives.LONGDOUBLE));

		// https://en.cppreference.com/w/c/numeric/math/expm1
		result.add(new Pair<>("expm1", CPrimitives.DOUBLE));
		result.add(new Pair<>("expm1f", CPrimitives.FLOAT));
		result.add(new Pair<>("expm1l", CPrimitives.LONGDOUBLE));

		// https://en.cppreference.com/w/c/numeric/math/tanh
		result.add(new Pair<>("tanh", CPrimitives.DOUBLE));
		result.add(new Pair<>("tanhf", CPrimitives.FLOAT));
		result.add(new Pair<>("tanhl", CPrimitives.LONGDOUBLE));

		// https://en.cppreference.com/w/c/numeric/math/erf
		result.add(new Pair<>("erf", CPrimitives.DOUBLE));
		result.add(new Pair<>("erff", CPrimitives.FLOAT));
		result.add(new Pair<>("erfl", CPrimitives.LONGDOUBLE));

		// https://en.cppreference.com/w/c/numeric/math/log
		result.add(new Pair<>("log", CPrimitives.DOUBLE));
		result.add(new Pair<>("logf", CPrimitives.FLOAT));
		result.add(new Pair<>("logl", CPrimitives.LONGDOUBLE));

		// https://en.cppreference.com/w/c/numeric/math/cos
		result.add(new Pair<>("cos", CPrimitives.DOUBLE));
		result.add(new Pair<>("cosf", CPrimitives.FLOAT));
		result.add(new Pair<>("cosl", CPrimitives.LONGDOUBLE));

		// https://en.cppreference.com/w/c/numeric/math/log1p
		result.add(new Pair<>("log1p", CPrimitives.DOUBLE));
		result.add(new Pair<>("log1pf", CPrimitives.FLOAT));
		result.add(new Pair<>("log1pl", CPrimitives.LONGDOUBLE));

		// https://en.cppreference.com/w/c/numeric/math/rint
		result.add(new Pair<>("rint", CPrimitives.DOUBLE));
		result.add(new Pair<>("rintf", CPrimitives.FLOAT));
		result.add(new Pair<>("rintl", CPrimitives.LONGDOUBLE));

		// https://en.cppreference.com/w/c/numeric/math/atanh
		result.add(new Pair<>("atanh", CPrimitives.DOUBLE));
		result.add(new Pair<>("atanhf", CPrimitives.FLOAT));
		result.add(new Pair<>("atanhl", CPrimitives.LONGDOUBLE));

		// https://en.cppreference.com/w/c/numeric/math/asin
		result.add(new Pair<>("asin", CPrimitives.DOUBLE));
		result.add(new Pair<>("asinf", CPrimitives.FLOAT));
		result.add(new Pair<>("asinl", CPrimitives.LONGDOUBLE));

		// https://en.cppreference.com/w/c/numeric/math/acos
		result.add(new Pair<>("acos", CPrimitives.DOUBLE));
		result.add(new Pair<>("acosf", CPrimitives.FLOAT));
		result.add(new Pair<>("acosl", CPrimitives.LONGDOUBLE));

		// https://en.cppreference.com/w/c/numeric/math/nearbyint
		result.add(new Pair<>("nearbyint", CPrimitives.DOUBLE));
		result.add(new Pair<>("nearbyintf", CPrimitives.FLOAT));
		result.add(new Pair<>("nearbyintl", CPrimitives.LONGDOUBLE));

		// http://en.cppreference.com/w/c/numeric/math/signbit
		result.add(new Pair<>("signbit", CPrimitives.INT));
		result.add(new Pair<>("__signbit", CPrimitives.INT));
		result.add(new Pair<>("__signbitl", CPrimitives.INT));
		result.add(new Pair<>("__signbitf", CPrimitives.INT));

		// http://en.cppreference.com/w/c/numeric/math/atan
		result.add(new Pair<>("atan", CPrimitives.DOUBLE));
		result.add(new Pair<>("atanf", CPrimitives.FLOAT));
		result.add(new Pair<>("atanl", CPrimitives.LONGDOUBLE));

		// http://en.cppreference.com/w/c/numeric/math/atan2
		result.add(new Pair<>("atan2", CPrimitives.DOUBLE));
		result.add(new Pair<>("atan2f", CPrimitives.FLOAT));
		result.add(new Pair<>("atan2l", CPrimitives.LONGDOUBLE));

		// http://en.cppreference.com/w/c/numeric/math/tan
		result.add(new Pair<>("tan", CPrimitives.DOUBLE));
		result.add(new Pair<>("tanf", CPrimitives.FLOAT));
		result.add(new Pair<>("tanl", CPrimitives.LONGDOUBLE));

		// http://en.cppreference.com/w/c/numeric/math/cosh
		result.add(new Pair<>("cosh", CPrimitives.DOUBLE));
		result.add(new Pair<>("coshf", CPrimitives.FLOAT));
		result.add(new Pair<>("coshl", CPrimitives.LONGDOUBLE));

		// http://en.cppreference.com/w/c/numeric/math/sinh
		result.add(new Pair<>("sinh", CPrimitives.DOUBLE));
		result.add(new Pair<>("sinhf", CPrimitives.FLOAT));
		result.add(new Pair<>("sinhl", CPrimitives.LONGDOUBLE));

		// http://en.cppreference.com/w/c/numeric/math/acosh
		result.add(new Pair<>("acosh", CPrimitives.DOUBLE));
		result.add(new Pair<>("acoshf", CPrimitives.FLOAT));
		result.add(new Pair<>("acoshl", CPrimitives.LONGDOUBLE));

		// http://en.cppreference.com/w/c/numeric/math/asinh
		result.add(new Pair<>("asinh", CPrimitives.DOUBLE));
		result.add(new Pair<>("asinhf", CPrimitives.FLOAT));
		result.add(new Pair<>("asinhl", CPrimitives.LONGDOUBLE));

		// http://en.cppreference.com/w/c/numeric/math/log10
		result.add(new Pair<>("log10", CPrimitives.DOUBLE));
		result.add(new Pair<>("log10f", CPrimitives.FLOAT));
		result.add(new Pair<>("log10l", CPrimitives.LONGDOUBLE));

		// http://en.cppreference.com/w/c/numeric/math/logb
		result.add(new Pair<>("logb", CPrimitives.DOUBLE));
		result.add(new Pair<>("logbf", CPrimitives.FLOAT));
		result.add(new Pair<>("logbl", CPrimitives.LONGDOUBLE));

		// http://en.cppreference.com/w/c/numeric/math/exp2
		result.add(new Pair<>("exp2", CPrimitives.DOUBLE));
		result.add(new Pair<>("exp2f", CPrimitives.FLOAT));
		result.add(new Pair<>("exp2l", CPrimitives.LONGDOUBLE));

		// http://en.cppreference.com/w/c/numeric/math/log2
		result.add(new Pair<>("log2", CPrimitives.DOUBLE));
		result.add(new Pair<>("log2f", CPrimitives.FLOAT));
		result.add(new Pair<>("log2l", CPrimitives.LONGDOUBLE));

		return result;
	}

	private static List<Pair<String, CPrimitives>> getOverapproximatedBinaryFunctions() {
		final List<Pair<String, CPrimitives>> result = new ArrayList<>();

		// see 7.12.10.2 or http://en.cppreference.com/w/c/numeric/math/remainder
		result.add(new Pair<>("remainder", CPrimitives.DOUBLE));
		result.add(new Pair<>("remainderf", CPrimitives.FLOAT));
		result.add(new Pair<>("remainderl", CPrimitives.LONGDOUBLE));

		// see 7.12.11.1 or http://en.cppreference.com/w/c/numeric/math/copysign
		result.add(new Pair<>("copysign", CPrimitives.DOUBLE));
		result.add(new Pair<>("copysignf", CPrimitives.FLOAT));
		result.add(new Pair<>("copysignl", CPrimitives.LONGDOUBLE));

		return result;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();
		for (final var overapprox : getOverapproximatedUnaryFunctions()) {
			result.add(
					new FunctionModel(overapprox.getFirst(), (main, node, loc, name) -> handleByOverapproximation(main,
							node, loc, name, 1, new CPrimitive(overapprox.getSecond()))));
		}
		for (final var overapprox : getOverapproximatedBinaryFunctions()) {
			result.add(
					new FunctionModel(overapprox.getFirst(), (main, node, loc, name) -> handleByOverapproximation(main,
							node, loc, name, 2, new CPrimitive(overapprox.getSecond()))));
		}
		for (final String unary : UNARY_FUNCTIONS) {
			result.add(new FunctionModel(unary, this::handleUnaryFloatFunction));
		}
		for (final String binary : BINARY_FUNCTIONS) {
			result.add(new FunctionModel(binary, this::handleBinaryFloatFunction));
		}

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
		result.add(new FunctionModel("__builtin_isnan",
				(main, node, loc, name) -> handleUnaryFloatFunction(main, node, loc, "isnan")));

		/** from fenv.h */
		result.add(new FunctionModel("fegetround", this::handleBuiltinFegetround));
		result.add(new FunctionModel("fesetround", this::handleBuiltinFesetround));

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

	private Result handleBuiltinFegetround(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 0, name, arguments);
		final RValue rvalue = mExpressionTranslation.constructBuiltinFegetround(loc);

		return new ExpressionResultBuilder().setLrValue(rvalue).build();
	}

	private Result handleBuiltinFesetround(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);

		final ExpressionResult decayedArgument =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult convertedArgument =
				mExprResultTransformer.convertIfNecessary(loc, decayedArgument, new CPrimitive(CPrimitives.INT));

		return mExpressionTranslation.constructBuiltinFesetround(loc, convertedArgument, mAuxVarInfoBuilder);
	}
}
