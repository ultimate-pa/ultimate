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

import java.math.BigInteger;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.BitvectorTranslation.SmtRoundingMode;
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

	private static final List<String> UNARY_FUNCTIONS = List.of("cos", "cosf", "cosl",

			"sin", "sinf", "sinl",

			"exp", "expf", "expl",

			"expm1", "expm1f", "expm1l",

			"log", "logf", "logl",

			"erf", "erff", "erfl",

			"tanh", "tanhf", "tanhl");

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
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	public MathLibraryModel(final FunctionModelHelper helper, final ExpressionResultTransformer exprResultTransformer,
			final ExpressionTranslation expressionTranslation, final CExpressionTranslator cEpressionTranslator,
			final INameHandler nameHandler, final AuxVarInfoBuilder auxVarInfoBuilder) {
		mHelper = helper;
		mExprResultTransformer = exprResultTransformer;
		mExpressionTranslation = expressionTranslation;
		mCEpressionTranslator = cEpressionTranslator;
		mNameHandler = nameHandler;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
	}

	private static List<Pair<String, CPrimitives>> getOverapproximatedUnaryFunctions() {
		final List<Pair<String, CPrimitives>> result = new ArrayList<>();

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

		// see 7.12.7.5 or http://en.cppreference.com/w/c/numeric/math/sqrt
		result.add(new FunctionModel("sqrt",
				(main, node, loc, name) -> handleSqrt(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("sqrtf",
				(main, node, loc, name) -> handleSqrt(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("sqrtl",
				(main, node, loc, name) -> handleSqrt(main, node, loc, name, new CPrimitive(CPrimitives.LONGDOUBLE))));

		// see 7.12.9.8 or http://en.cppreference.com/w/c/numeric/math/trunc
		result.add(new FunctionModel("trunc", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.DOUBLE), SmtRoundingMode.RTZ)));
		result.add(new FunctionModel("truncf", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.FLOAT), SmtRoundingMode.RTZ)));
		result.add(new FunctionModel("truncl", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.LONGDOUBLE), SmtRoundingMode.RTZ)));

		// see 7.12.9.2 or http://en.cppreference.com/w/c/numeric/math/floor
		result.add(new FunctionModel("floor", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.DOUBLE), SmtRoundingMode.RTN)));
		result.add(new FunctionModel("floorf", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.FLOAT), SmtRoundingMode.RTN)));
		result.add(new FunctionModel("floorl", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.LONGDOUBLE), SmtRoundingMode.RTN)));

		// see 7.12.9.1 or http://en.cppreference.com/w/c/numeric/math/ceil
		result.add(new FunctionModel("ceil", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.DOUBLE), SmtRoundingMode.RTP)));
		result.add(new FunctionModel("ceilf", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.FLOAT), SmtRoundingMode.RTP)));
		result.add(new FunctionModel("ceill", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.LONGDOUBLE), SmtRoundingMode.RTP)));

		// see 7.12.9.6 or http://en.cppreference.com/w/c/numeric/math/round
		result.add(new FunctionModel("round", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.DOUBLE), SmtRoundingMode.RNA)));
		result.add(new FunctionModel("roundf", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.FLOAT), SmtRoundingMode.RNA)));
		result.add(new FunctionModel("roundl", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.LONGDOUBLE), SmtRoundingMode.RNA)));

		// see 7.12.9.7 or http://en.cppreference.com/w/c/numeric/math/round
		result.add(new FunctionModel("lround", (main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc,
				name, new CPrimitive(CPrimitives.DOUBLE), new CPrimitive(CPrimitives.LONG), SmtRoundingMode.RNA)));
		result.add(new FunctionModel("lroundf", (main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc,
				name, new CPrimitive(CPrimitives.FLOAT), new CPrimitive(CPrimitives.LONG), SmtRoundingMode.RNA)));
		result.add(new FunctionModel("lroundl", (main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc,
				name, new CPrimitive(CPrimitives.LONGDOUBLE), new CPrimitive(CPrimitives.LONG), SmtRoundingMode.RNA)));
		result.add(new FunctionModel("llround", (main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc,
				name, new CPrimitive(CPrimitives.DOUBLE), new CPrimitive(CPrimitives.LONGLONG), SmtRoundingMode.RNA)));
		result.add(new FunctionModel("llroundf",
				(main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc, name,
						new CPrimitive(CPrimitives.FLOAT), new CPrimitive(CPrimitives.LONGLONG), SmtRoundingMode.RNA)));
		result.add(new FunctionModel("llroundl",
				(main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc, name,
						new CPrimitive(CPrimitives.LONGDOUBLE), new CPrimitive(CPrimitives.LONGLONG),
						SmtRoundingMode.RNA)));

		// see 7.12.7.2 or http://en.cppreference.com/w/c/numeric/math/fabs
		result.add(new FunctionModel("fabs",
				(main, node, loc, name) -> handleFabs(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("fabsf",
				(main, node, loc, name) -> handleFabs(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("fabsl",
				(main, node, loc, name) -> handleFabs(main, node, loc, name, new CPrimitive(CPrimitives.LONGDOUBLE))));

		// see 7.12.3.4 or http://en.cppreference.com/w/c/numeric/math/isnan
		result.add(new FunctionModel("isnan", this::handleIsNan));
		result.add(new FunctionModel("__isnan", this::handleIsNan));

		// see https://linux.die.net/man/3/isnanf (! NOT PART OF ANSI-C)
		result.add(new FunctionModel("isnanf", this::handleIsNan));
		result.add(new FunctionModel("isnanl", this::handleIsNan));
		result.add(new FunctionModel("__isnanf", this::handleIsNan));
		result.add(new FunctionModel("__isnanl", this::handleIsNan));

		// see 7.12.3.3 or http://en.cppreference.com/w/c/numeric/math/isinf
		result.add(new FunctionModel("isinf", this::handleIsInf));
		result.add(new FunctionModel("__isinf", this::handleIsInf));
		result.add(new FunctionModel("__builtin_isinf_sign", this::handleIsInfSign));

		// see https://linux.die.net/man/3/isinff (! NOT PART OF ANSI-C)
		result.add(new FunctionModel("isinff", this::handleIsFinite));
		result.add(new FunctionModel("isinfl", this::handleIsFinite));
		result.add(new FunctionModel("__isinff", this::handleIsFinite));
		result.add(new FunctionModel("__isinfl", this::handleIsFinite));

		// see 7.12.3.2 or http://en.cppreference.com/w/c/numeric/math/isfinite
		result.add(new FunctionModel("isfinite", this::handleIsFinite));

		// see https://linux.die.net/man/3/finite (! NOT PART OF ANSI-C)
		result.add(new FunctionModel("finite", this::handleIsFinite));
		result.add(new FunctionModel("finitel", this::handleIsFinite));
		result.add(new FunctionModel("__finite", this::handleIsFinite));
		result.add(new FunctionModel("__finitef", this::handleIsFinite));
		result.add(new FunctionModel("__finitel", this::handleIsFinite));

		// see 7.12.3.1 or http://en.cppreference.com/w/c/numeric/math/fpclassify
		result.add(new FunctionModel("fpclassify", this::handleFpClassify));
		result.add(new FunctionModel("__fpclassify", this::handleFpClassify));
		result.add(new FunctionModel("__fpclassifyf", this::handleFpClassify));
		result.add(new FunctionModel("__fpclassifyl", this::handleFpClassify));

		// see 7.12.3.5 or http://en.cppreference.com/w/c/numeric/math/isnormal
		result.add(new FunctionModel("isnormal", this::handleIsNormal));

		// https://en.cppreference.com/w/c/numeric/math/copysign

		// TODO: Handle negative NaN, check unsoundness
		// if second is negative, return arithneg of abs(first), else return abs(first)
		// final FloatFunction absfloatFunction = FloatFunction.decode("fabs");
		// final RValue absoluteValue = constructOtherUnaryFloatOperation(loc, absfloatFunction, first);
		//
		// final String smtNegativeFunctionName = "fp.isNegative";
		// final RValue secondNegativeRvalue =
		// constructSmtFloatClassificationFunction(loc, smtNegativeFunctionName, second);
		// final Expression isNegativeSecond = secondNegativeRvalue.getValue();
		// final CPrimitive resultType = (CPrimitive) first.getCType().getUnderlyingType();
		// final Expression negative = constructUnaryFloatingPointExpression(loc, IASTUnaryExpression.op_minus,
		// absoluteValue.getValue(), resultType);
		// final Expression resultExpr = ExpressionFactory.constructIfThenElseExpression(loc, isNegativeSecond,
		// negative, absoluteValue.getValue());
		// return new RValue(resultExpr, resultType);

		// https://en.cppreference.com/w/c/numeric/math/signbit

		// TODO: Handle negative NaN correctly
		// final Expression isNegative;
		// final String smtFunctionName = "fp.isNegative";
		// final RValue rvalue = constructSmtFloatClassificationFunction(loc, smtFunctionName, argument);
		// isNegative = rvalue.getValue();
		//
		// final CPrimitive cPrimitive = new CPrimitive(CPrimitives.INT);
		// final Expression resultExpr = ExpressionFactory.constructIfThenElseExpression(loc, isNegative,
		// mTypeSizes.constructLiteralForIntegerType(loc, cPrimitive, BigInteger.ONE),
		// mTypeSizes.constructLiteralForIntegerType(loc, cPrimitive, BigInteger.ZERO));
		// return new RValue(resultExpr, cPrimitive);

		/** various float builtins **/
		result.add(new FunctionModel("nan",
				(main, node, loc, name) -> handleNan(loc, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("nanf",
				(main, node, loc, name) -> handleNan(loc, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("nanl",
				(main, node, loc, name) -> handleNan(loc, new CPrimitive(CPrimitives.LONGDOUBLE))));
		result.add(new FunctionModel("__builtin_nan",
				(main, node, loc, name) -> handleNan(loc, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("__builtin_nanf",
				(main, node, loc, name) -> handleNan(loc, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("__builtin_nanl",
				(main, node, loc, name) -> handleNan(loc, new CPrimitive(CPrimitives.LONGDOUBLE))));
		result.add(new FunctionModel("__builtin_inff", (main, node, loc, name) -> handleInf(loc)));
		result.add(new FunctionModel("__builtin_huge_val", (main, node, loc, name) -> handleInf(loc)));
		result.add(new FunctionModel("__builtin_huge_valf", (main, node, loc, name) -> handleInf(loc)));
		result.add(new FunctionModel("__builtin_isgreater", this::handleIsGreater));
		result.add(new FunctionModel("__builtin_isgreaterequal", this::handleIsGreaterEqual));
		result.add(new FunctionModel("__builtin_isless", this::handleIsLess));
		result.add(new FunctionModel("__builtin_islessequal", this::handleIsLessEqual));
		result.add(new FunctionModel("__builtin_isunordered", this::handleIsUnordered));
		result.add(new FunctionModel("__builtin_islessgreater", this::handleIsLessGreater));
		result.add(new FunctionModel("__builtin_isnan", this::handleIsNan));

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

	private ExpressionResult handleNan(final ILocation loc, final CPrimitive type) {
		return new ExpressionResult(new RValue(mExpressionTranslation.createNan(loc, type), type));
	}

	private ExpressionResult handleInf(final ILocation loc) {
		final CPrimitive type = new CPrimitive(CPrimitives.DOUBLE);
		return new ExpressionResult(new RValue(mExpressionTranslation.createPlusInfinity(loc, type), type));
	}

	private Result handleUnaryFloatFunction(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final FloatFunction floatFunction = FloatFunction.decode(name);
		final ExpressionResult arg = handleFloatArguments(main, node, loc, name, 1, floatFunction).get(0);
		return new ExpressionResultBuilder().addAllExceptLrValue(arg).addAllIncludingLrValue(mExpressionTranslation
				.constructOtherUnaryFloatOperation(loc, floatFunction, (RValue) arg.getLrValue(), mAuxVarInfoBuilder))
				.build();
	}

	private Result handleBinaryFloatFunction(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final FloatFunction floatFunction = FloatFunction.decode(name);
		final List<ExpressionResult> args = handleFloatArguments(main, node, loc, name, 2, floatFunction);
		return new ExpressionResultBuilder().addAllExceptLrValue(args)
				.addAllIncludingLrValue(mExpressionTranslation.constructOtherBinaryFloatOperation(loc, floatFunction,
						(RValue) args.get(0).getLrValue(), (RValue) args.get(1).getLrValue(), mAuxVarInfoBuilder))
				.build();
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

	private List<ExpressionResult> handleFloatArguments(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final int numberOfArgs, final CPrimitive type) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, numberOfArgs, name, arguments);
		final List<ExpressionResult> rtr = new ArrayList<>();
		for (final IASTInitializerClause argument : arguments) {
			final ExpressionResult decayedArgument =
					mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, argument);
			final ExpressionResult convertedArgument =
					mExprResultTransformer.convertIfNecessary(loc, decayedArgument, type);
			rtr.add(convertedArgument);
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
		final Expression leftExpr = mExpressionTranslation.isNan(loc, leftRvaluedResult.getLrValue().getValue(),
				(CPrimitive) leftRvaluedResult.getCType());
		final Expression rightExpr = mExpressionTranslation.isNan(loc, rightRvaluedResult.getLrValue().getValue(),
				(CPrimitive) rightRvaluedResult.getCType());
		final Expression expr = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftExpr, rightExpr);
		final LRValue lrVal = new RValue(expr, new CPrimitive(CPrimitives.INT), true);
		final ExpressionResult rtr = new ExpressionResultBuilder()
				.addAllExceptLrValue(leftRvaluedResult, rightRvaluedResult).setLrValue(lrVal).build();
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

	private ExpressionResult handleSqrt(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final ExpressionResult argumentResult = handleFloatArguments(main, node, loc, name, 1, type).getFirst();
		return new ExpressionResultBuilder().addAllExceptLrValue(argumentResult).setLrValue(
				new RValue(mExpressionTranslation.sqrt(loc, argumentResult.getLrValue().getValue(), type), type))
				.build();
	}

	private ExpressionResult handleRound(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type, final SmtRoundingMode roundingMode) {
		final ExpressionResult argumentResult = handleFloatArguments(main, node, loc, name, 1, type).getFirst();
		return new ExpressionResultBuilder().addAllExceptLrValue(argumentResult).setLrValue(new RValue(
				mExpressionTranslation.roundToIntegral(loc, argumentResult.getLrValue().getValue(), type, roundingMode),
				type)).build();
	}

	private ExpressionResult handleRoundWithIntConversion(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type, final CPrimitive resultType,
			final SmtRoundingMode roundingMode) {
		return mExpressionTranslation.convertFloatToInt(loc,
				handleRound(main, node, loc, name, resultType, roundingMode), resultType);
	}

	private ExpressionResult handleFabs(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final ExpressionResult argumentResult = handleFloatArguments(main, node, loc, name, 1, type).getFirst();
		return new ExpressionResultBuilder().addAllExceptLrValue(argumentResult)
				.setLrValue(
						new RValue(mExpressionTranslation.abs(loc, argumentResult.getLrValue().getValue(), type), type))
				.build();
	}

	private ExpressionResult handleIsNan(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);
		final ExpressionResult argumentResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		return new ExpressionResultBuilder().addAllExceptLrValue(argumentResult)
				.setLrValue(new RValue(mExpressionTranslation.isNan(loc, argumentResult.getLrValue().getValue(),
						(CPrimitive) argumentResult.getCType()), new CPrimitive(CPrimitives.INT), true))
				.build();
	}

	private ExpressionResult handleIsInf(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);
		final ExpressionResult argumentResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		return new ExpressionResultBuilder().addAllExceptLrValue(argumentResult)
				.setLrValue(new RValue(mExpressionTranslation.isInfinite(loc, argumentResult.getLrValue().getValue(),
						(CPrimitive) argumentResult.getCType()), new CPrimitive(CPrimitives.INT), true))
				.build();
	}

	private ExpressionResult handleIsInfSign(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);
		final ExpressionResult argumentResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final CPrimitive intType = new CPrimitive(CPrimitives.INT);
		final Expression argument = argumentResult.getLrValue().getValue();
		final CPrimitive type = (CPrimitive) argumentResult.getCType();
		final Expression isInfinite = mExpressionTranslation.isInfinite(loc, argument, type);
		final Expression isPositive = mExpressionTranslation.isPositive(loc, argument, type);
		final Expression resultExpr = ExpressionFactory.constructIfThenElseExpression(loc, isInfinite,
				ExpressionFactory.constructIfThenElseExpression(loc, isPositive,
						mExpressionTranslation.constructLiteralForIntegerType(loc, intType, BigInteger.ONE),
						mExpressionTranslation.constructLiteralForIntegerType(loc, intType, BigInteger.ONE.negate())),
				mExpressionTranslation.constructLiteralForIntegerType(loc, intType, BigInteger.ZERO));
		return new ExpressionResultBuilder().addAllExceptLrValue(argumentResult)
				.setLrValue(new RValue(resultExpr, new CPrimitive(CPrimitives.INT))).build();
	}

	private ExpressionResult handleIsFinite(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);
		final ExpressionResult argumentResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final Expression argument = argumentResult.getLrValue().getValue();
		final CPrimitive type = (CPrimitive) argumentResult.getCType();
		final Expression resultExpr = ExpressionFactory.or(loc, mExpressionTranslation.isNormal(loc, argument, type),
				mExpressionTranslation.isSubnormal(loc, argument, type),
				mExpressionTranslation.isZero(loc, argument, type));
		return new ExpressionResultBuilder().addAllExceptLrValue(argumentResult)
				.setLrValue(new RValue(resultExpr, new CPrimitive(CPrimitives.INT), true)).build();
	}

	private ExpressionResult handleFpClassify(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);
		final ExpressionResult argumentResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final Expression argument = argumentResult.getLrValue().getValue();
		final CPrimitive type = (CPrimitive) argumentResult.getCType();
		final Expression isInfinite = mExpressionTranslation.isInfinite(loc, argument, type);
		final Expression isNan = mExpressionTranslation.isNan(loc, argument, type);
		final Expression isNormal = mExpressionTranslation.isNormal(loc, argument, type);
		final Expression isSubnormal = mExpressionTranslation.isSubnormal(loc, argument, type);
		final Expression resultExpr = ExpressionFactory.constructIfThenElseExpression(loc, isInfinite,
				mExpressionTranslation.handleNumberClassificationMacro(loc, "FP_INFINITE").getValue(),
				ExpressionFactory.constructIfThenElseExpression(loc, isNan,
						mExpressionTranslation.handleNumberClassificationMacro(loc, "FP_NAN").getValue(),
						ExpressionFactory.constructIfThenElseExpression(loc, isNormal,
								mExpressionTranslation.handleNumberClassificationMacro(loc, "FP_NORMAL").getValue(),
								ExpressionFactory.constructIfThenElseExpression(loc, isSubnormal,
										mExpressionTranslation.handleNumberClassificationMacro(loc, "FP_SUBNORMAL")
												.getValue(),
										mExpressionTranslation.handleNumberClassificationMacro(loc, "FP_ZERO")
												.getValue()))));
		return new ExpressionResultBuilder().addAllExceptLrValue(argumentResult)
				.setLrValue(new RValue(resultExpr, new CPrimitive(CPrimitives.INT))).build();
	}

	private ExpressionResult handleIsNormal(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);
		final ExpressionResult argumentResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		return new ExpressionResultBuilder().addAllExceptLrValue(argumentResult)
				.setLrValue(new RValue(mExpressionTranslation.isNormal(loc, argumentResult.getLrValue().getValue(),
						(CPrimitive) argumentResult.getCType()), new CPrimitive(CPrimitives.INT), true))
				.build();
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
		return List.of(new ConstantModel("NAN", loc -> handleNan(loc, new CPrimitive(CPrimitives.DOUBLE))),
				new ConstantModel("INFINITY", loc -> handleInf(loc)), new ConstantModel("inf", loc -> handleInf(loc)),
				// Check if id is number classification macro according to 7.12.6 of C11.
				modelNumberClassificationMacro("FP_NAN"), modelNumberClassificationMacro("FP_INFINITE"),
				modelNumberClassificationMacro("FP_ZERO"), modelNumberClassificationMacro("FP_SUBNORMAL"),
				modelNumberClassificationMacro("FP_NORMAL"));
	}
}
