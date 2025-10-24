/*
 * Copyright (C) 2013-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2020 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021-2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022-2025 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2025 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CExpressionTranslator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.FloatFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Model of functions from math.h (C11 7.12, https://en.cppreference.com/w/c/header/math)
 */
public class MathLibraryModel implements ILibraryModel {
	private final static String[] UNSUPPORTED_FLOAT_OPERATIONS = { "frexp", "ldexp", "pow", "hypot", "cbrt", "drem",
			"significand", "j0", "j1", "jn", "y0", "y1", "yn", "erfc", "lgamma", "tgamma", "gamma", "lgamma_r",
			"nextafter", "nexttoward", "scalbn", "ilogb", "scalbln", "remquo", "lrint", "llrint", "fma", "scalb",
			"frexpf", "ldexpf", "powf", "hypotf", "cbrtf", "dremf", "significandf", "j0f", "j1f", "jnf", "y0f", "y1f",
			"ynf", "erfcf", "lgammaf", "tgammaf", "gammaf", "lgammaf_r", "nextafterf", "nexttowardf", "scalbnf",
			"ilogbf", "scalblnf", "remquof", "lrintf", "llrintf", "fmaf", "scalbf", "frexpl", "ldexpl", "powl",
			"hypotl", "cbrtl", "dreml", "significandl", "j0l", "j1l", "jnl", "y0l", "y1l", "ynl", "erfcl", "lgammal",
			"tgammal", "gammal", "lgammal_r", "nextafterl", "nexttowardl", "scalbnl", "ilogbl", "scalblnl", "remquol",
			"lrintl", "llrintl", "fmal", "scalbl", "signgam;", "modf", "modff", "modfl" };

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
			"finite", "__finite", "finitef", "__finitef", "finitel", "__finitel", "isinff", "__isinff", "isinfl",
			"__isinfl", "isnanf", "isnanl", "__isnanf", "__isnanl",

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
			"ceil", "ceilf", "ceilr");

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
			"fdim", "fdimf", "fdiml");

	private final FunctionModelHelper mHelper;
	private final ExpressionResultTransformer mExprResultTransformer;
	private final ExpressionTranslation mExpressionTranslation;
	private final CExpressionTranslator mCEpressionTranslator;
	private final INameHandler mNameHandler;

	public MathLibraryModel(final FunctionModelHelper helper, final ExpressionResultTransformer exprResultTransformer,
			final ExpressionTranslation expressionTranslation, final CExpressionTranslator cEpressionTranslator,
			final INameHandler nameHandler) {
		mHelper = helper;
		mExprResultTransformer = exprResultTransformer;
		mExpressionTranslation = expressionTranslation;
		mCEpressionTranslator = cEpressionTranslator;
		mNameHandler = nameHandler;
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
			result.add(new FunctionModel(overapprox.getFirst(), (main, node, loc, name) -> mHelper
					.handleByOverapproximation(main, node, loc, name, 1, new CPrimitive(overapprox.getSecond()))));
		}
		for (final var overapprox : getOverapproximatedBinaryFunctions()) {
			result.add(new FunctionModel(overapprox.getFirst(), (main, node, loc, name) -> mHelper
					.handleByOverapproximation(main, node, loc, name, 2, new CPrimitive(overapprox.getSecond()))));
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
		result.add(new FunctionModel("__builtin_isgreater", this::handleIsGreater));
		result.add(new FunctionModel("__builtin_isgreaterequal", this::handleIsGreaterEqual));
		result.add(new FunctionModel("__builtin_isless", this::handleIsLess));
		result.add(new FunctionModel("__builtin_islessequal", this::handleIsLessEqual));
		result.add(new FunctionModel("__builtin_isunordered", this::handleIsUnordered));
		result.add(new FunctionModel("__builtin_islessgreater", this::handleIsLessGreater));
		result.add(new FunctionModel("__builtin_isnan",
				(main, node, loc, name) -> handleUnaryFloatFunction(main, node, loc, "isnan")));

		result.add(new FunctionModel("isgreater", this::handleIsGreater));
		result.add(new FunctionModel("isgreaterequal", this::handleIsGreaterEqual));
		result.add(new FunctionModel("isless", this::handleIsLess));
		result.add(new FunctionModel("islessequal", this::handleIsLessEqual));
		result.add(new FunctionModel("isunordered", this::handleIsUnordered));
		result.add(new FunctionModel("islessgreater", this::handleIsLessGreater));

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
		mHelper.checkArguments(loc, numberOfArgs, name, arguments);
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

	// http://en.cppreference.com/w/c/numeric/math/isless
	private Result handleIsLess(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		return handleBinaryComparison(main, node, loc, name, IASTBinaryExpression.op_lessThan);
	}

	// http://en.cppreference.com/w/c/numeric/math/islessequal
	private Result handleIsLessEqual(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		return handleBinaryComparison(main, node, loc, name, IASTBinaryExpression.op_lessEqual);
	}

	// http://en.cppreference.com/w/c/numeric/math/isgreater
	private Result handleIsGreater(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		return handleBinaryComparison(main, node, loc, name, IASTBinaryExpression.op_greaterThan);
	}

	// http://en.cppreference.com/w/c/numeric/math/isgreaterequal
	private Result handleIsGreaterEqual(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		return handleBinaryComparison(main, node, loc, name, IASTBinaryExpression.op_greaterEqual);
	}

	private Result handleBinaryComparison(final IDispatcher main, final IASTFunctionCallExpression node,
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
		mHelper.checkArguments(loc, 2, name, arguments);

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
	private Result handleIsUnordered(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 2, name, arguments);

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

	private Result handleIsLessGreater(final IDispatcher main, final IASTFunctionCallExpression node,
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
		mHelper.checkArguments(loc, 2, name, arguments);

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

	@Override
	public Collection<TypeModel> getTypeModels() {
		return List.of(
				// most efficient floating-point type at least as wide as float -> We choose float
				new TypeModel("float_t", new CPrimitive(CPrimitives.FLOAT)),
				// most efficient floating-point type at least as wide as double -> We choose double
				new TypeModel("double_t", new CPrimitive(CPrimitives.DOUBLE)));
	}

	private ConstantModel modelNumberClassificationMacro(final String name) {
		return new ConstantModel(name,
				loc -> new ExpressionResult(mExpressionTranslation.handleNumberClassificationMacro(loc, name)));
	}

	@Override
	public Collection<ConstantModel> getConstantModels() {
		return List.of(new ConstantModel("NAN", loc -> mExpressionTranslation.createNanOrInfinity(loc, "NAN")),
				new ConstantModel("INFINITY", loc -> mExpressionTranslation.createNanOrInfinity(loc, "INFINITY")),
				new ConstantModel("inf", loc -> mExpressionTranslation.createNanOrInfinity(loc, "inf")),
				// Check if id is number classification macro according to 7.12.6 of C11.
				modelNumberClassificationMacro("FP_NAN"), modelNumberClassificationMacro("FP_INFINITE"),
				modelNumberClassificationMacro("FP_ZERO"), modelNumberClassificationMacro("FP_SUBNORMAL"),
				modelNumberClassificationMacro("FP_NORMAL"));
	}
}
