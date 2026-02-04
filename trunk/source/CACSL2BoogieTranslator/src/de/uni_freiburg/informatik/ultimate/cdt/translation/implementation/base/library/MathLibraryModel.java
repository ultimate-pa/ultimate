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

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CExpressionTranslator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.BitvectorTranslation.SmtRoundingMode;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.IFloatingPointHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.OverapproxVariable;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Model of functions from math.h (C11 7.12, https://en.cppreference.com/w/c/header/math)
 */
public class MathLibraryModel implements ILibraryModel {
	// Number classification macros according to 7.12.6 of C11
	private enum Classification {
		NAN("FP_NAN", 0), INFINITE("FP_INFINITE", 1), ZERO("FP_ZERO", 2), SUBNORMAL("FP_SUBNORMAL", 3),
		NORMAL("FP_NORMAL", 4);

		private final String mName;
		private final int mValue;

		Classification(final String name, final int value) {
			mName = name;
			mValue = value;
		}

		public String getName() {
			return mName;
		}

		public Expression asExpression(final ILocation loc, final ExpressionTranslation exprTranslation) {
			return exprTranslation.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT),
					BigInteger.valueOf(mValue));
		}
	}

	private final static String[] UNSUPPORTED_FLOAT_OPERATIONS = { "frexp", "ldexp", "pow", "hypot", "cbrt", "drem",
			"significand", "j0", "j1", "jn", "y0", "y1", "yn", "erfc", "lgamma", "tgamma", "gamma", "lgamma_r",
			"nextafter", "nexttoward", "scalbn", "ilogb", "scalbln", "remquo", "fma", "scalb", "frexpf", "ldexpf",
			"powf", "hypotf", "cbrtf", "dremf", "significandf", "j0f", "j1f", "jnf", "y0f", "y1f", "ynf", "erfcf",
			"lgammaf", "tgammaf", "gammaf", "lgammaf_r", "nextafterf", "nexttowardf", "scalbnf", "ilogbf", "scalblnf",
			"remquof", "fmaf", "scalbf", "frexpl", "ldexpl", "powl", "hypotl", "cbrtl", "dreml", "significandl", "j0l",
			"j1l", "jnl", "y0l", "y1l", "ynl", "erfcl", "lgammal", "tgammal", "gammal", "lgammal_r", "nextafterl",
			"nexttowardl", "scalbnl", "ilogbl", "scalblnl", "remquol", "fmal", "scalbl", "signgam;", "modf", "modff",
			"modfl" };

	private final FunctionModelHelper mHelper;
	private final ExpressionResultTransformer mExprResultTransformer;
	private final ExpressionTranslation mExpressionTranslation;
	private final IFloatingPointHandler mFloatHandler;
	private final CExpressionTranslator mCEpressionTranslator;
	private final INameHandler mNameHandler;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	public MathLibraryModel(final FunctionModelHelper helper, final ExpressionResultTransformer exprResultTransformer,
			final ExpressionTranslation expressionTranslation, final CExpressionTranslator cEpressionTranslator,
			final INameHandler nameHandler, final AuxVarInfoBuilder auxVarInfoBuilder) {
		mHelper = helper;
		mExprResultTransformer = exprResultTransformer;
		mExpressionTranslation = expressionTranslation;
		mFloatHandler = expressionTranslation.getFloatingPointHandler();
		mCEpressionTranslator = cEpressionTranslator;
		mNameHandler = nameHandler;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();

		// see 7.12.7.5 or http://en.cppreference.com/w/c/numeric/math/sqrt
		result.add(new FunctionModel("sqrt",
				(main, node, loc, name) -> handleSqrt(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("sqrtf",
				(main, node, loc, name) -> handleSqrt(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("sqrtl",
				(main, node, loc, name) -> handleSqrt(main, node, loc, name, new CPrimitive(CPrimitives.LONGDOUBLE))));

		final Expression roundTowardsZero = SmtRoundingMode.RTZ.getBoogieIdentifierExpression();
		final Expression roundTowardsNegative = SmtRoundingMode.RTN.getBoogieIdentifierExpression();
		final Expression roundTowardsPositive = SmtRoundingMode.RTP.getBoogieIdentifierExpression();
		final Expression roundToNearest = SmtRoundingMode.RNA.getBoogieIdentifierExpression();

		// see 7.12.9.8 or http://en.cppreference.com/w/c/numeric/math/trunc
		result.add(new FunctionModel("trunc", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.DOUBLE), roundTowardsZero)));
		result.add(new FunctionModel("truncf", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.FLOAT), roundTowardsZero)));
		result.add(new FunctionModel("truncl", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.LONGDOUBLE), roundTowardsZero)));

		// see 7.12.9.2 or http://en.cppreference.com/w/c/numeric/math/floor
		result.add(new FunctionModel("floor", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.DOUBLE), roundTowardsNegative)));
		result.add(new FunctionModel("floorf", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.FLOAT), roundTowardsNegative)));
		result.add(new FunctionModel("floorl", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.LONGDOUBLE), roundTowardsNegative)));

		// see 7.12.9.1 or http://en.cppreference.com/w/c/numeric/math/ceil
		result.add(new FunctionModel("ceil", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.DOUBLE), roundTowardsPositive)));
		result.add(new FunctionModel("ceilf", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.FLOAT), roundTowardsPositive)));
		result.add(new FunctionModel("ceill", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.LONGDOUBLE), roundTowardsPositive)));

		// see 7.12.9.6 or http://en.cppreference.com/w/c/numeric/math/round
		result.add(new FunctionModel("round", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.DOUBLE), roundToNearest)));
		result.add(new FunctionModel("roundf", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.FLOAT), roundToNearest)));
		result.add(new FunctionModel("roundl", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.LONGDOUBLE), roundToNearest)));

		// see 7.12.9.7 or http://en.cppreference.com/w/c/numeric/math/round
		result.add(new FunctionModel("lround", (main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc,
				name, new CPrimitive(CPrimitives.DOUBLE), new CPrimitive(CPrimitives.LONG), roundToNearest)));
		result.add(new FunctionModel("lroundf", (main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc,
				name, new CPrimitive(CPrimitives.FLOAT), new CPrimitive(CPrimitives.LONG), roundToNearest)));
		result.add(new FunctionModel("lroundl", (main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc,
				name, new CPrimitive(CPrimitives.LONGDOUBLE), new CPrimitive(CPrimitives.LONG), roundToNearest)));
		result.add(new FunctionModel("llround", (main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc,
				name, new CPrimitive(CPrimitives.DOUBLE), new CPrimitive(CPrimitives.LONGLONG), roundToNearest)));
		result.add(new FunctionModel("llroundf", (main, node, loc, name) -> handleRoundWithIntConversion(main, node,
				loc, name, new CPrimitive(CPrimitives.FLOAT), new CPrimitive(CPrimitives.LONGLONG), roundToNearest)));
		result.add(new FunctionModel("llroundl",
				(main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc, name,
						new CPrimitive(CPrimitives.LONGDOUBLE), new CPrimitive(CPrimitives.LONGLONG), roundToNearest)));

		// https://en.cppreference.com/w/c/numeric/math/rint
		result.add(new FunctionModel("rint", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.DOUBLE), mExpressionTranslation.getCurrentRoundingMode())));
		result.add(new FunctionModel("rintf", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.FLOAT), mExpressionTranslation.getCurrentRoundingMode())));
		result.add(new FunctionModel("rintl", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.LONGDOUBLE), mExpressionTranslation.getCurrentRoundingMode())));
		result.add(new FunctionModel("lrint",
				(main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc, name,
						new CPrimitive(CPrimitives.DOUBLE), new CPrimitive(CPrimitives.LONG),
						mExpressionTranslation.getCurrentRoundingMode())));
		result.add(new FunctionModel("lrintf",
				(main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc, name,
						new CPrimitive(CPrimitives.FLOAT), new CPrimitive(CPrimitives.LONG),
						mExpressionTranslation.getCurrentRoundingMode())));
		result.add(new FunctionModel("lrintl",
				(main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc, name,
						new CPrimitive(CPrimitives.LONGDOUBLE), new CPrimitive(CPrimitives.LONG),
						mExpressionTranslation.getCurrentRoundingMode())));
		result.add(new FunctionModel("llrint",
				(main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc, name,
						new CPrimitive(CPrimitives.DOUBLE), new CPrimitive(CPrimitives.LONGLONG),
						mExpressionTranslation.getCurrentRoundingMode())));
		result.add(new FunctionModel("llrintf",
				(main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc, name,
						new CPrimitive(CPrimitives.FLOAT), new CPrimitive(CPrimitives.LONGLONG),
						mExpressionTranslation.getCurrentRoundingMode())));
		result.add(new FunctionModel("llrintl",
				(main, node, loc, name) -> handleRoundWithIntConversion(main, node, loc, name,
						new CPrimitive(CPrimitives.LONGDOUBLE), new CPrimitive(CPrimitives.LONGLONG),
						mExpressionTranslation.getCurrentRoundingMode())));

		// https://en.cppreference.com/w/c/numeric/math/nearbyint
		result.add(new FunctionModel("nearbyint", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.DOUBLE), mExpressionTranslation.getCurrentRoundingMode())));
		result.add(new FunctionModel("nearbyintf", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.FLOAT), mExpressionTranslation.getCurrentRoundingMode())));
		result.add(new FunctionModel("nearbyintl", (main, node, loc, name) -> handleRound(main, node, loc, name,
				new CPrimitive(CPrimitives.LONGDOUBLE), mExpressionTranslation.getCurrentRoundingMode())));

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
		result.add(new FunctionModel("isinff", this::handleIsInf));
		result.add(new FunctionModel("isinfl", this::handleIsInf));
		result.add(new FunctionModel("__isinff", this::handleIsInf));
		result.add(new FunctionModel("__isinfl", this::handleIsInf));

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

		// http://en.cppreference.com/w/c/numeric/math/signbit
		result.add(new FunctionModel("signbit", this::handleSignbit));
		result.add(new FunctionModel("__signbit", this::handleSignbit));
		result.add(new FunctionModel("__signbitl", this::handleSignbit));
		result.add(new FunctionModel("__signbitf", this::handleSignbit));

		// see 7.12.11.1 or http://en.cppreference.com/w/c/numeric/math/copysign
		// if second is negative, return -abs(first), else return abs(first)
		result.add(new FunctionModel("copysign",
				(main, node, loc, name) -> handleCopysign(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("copysignf",
				(main, node, loc, name) -> handleCopysign(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("copysignl", (main, node, loc, name) -> handleCopysign(main, node, loc, name,
				new CPrimitive(CPrimitives.LONGDOUBLE))));

		// see 7.12.4.5 or https://en.cppreference.com/w/c/numeric/math/cos
		result.add(new FunctionModel("cos",
				(main, node, loc, name) -> handleCos(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("cosf",
				(main, node, loc, name) -> handleCos(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("cosl",
				(main, node, loc, name) -> handleCos(main, node, loc, name, new CPrimitive(CPrimitives.LONGDOUBLE))));

		// see 7.12.4.6 or https://en.cppreference.com/w/c/numeric/math/sin
		result.add(new FunctionModel("sin",
				(main, node, loc, name) -> handleSin(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("sinf",
				(main, node, loc, name) -> handleSin(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("sinl",
				(main, node, loc, name) -> handleSin(main, node, loc, name, new CPrimitive(CPrimitives.LONGDOUBLE))));

		// see 7.12.6.1 or https://en.cppreference.com/w/c/numeric/math/exp
		result.add(new FunctionModel("exp",
				(main, node, loc, name) -> handleExp(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("expf",
				(main, node, loc, name) -> handleExp(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("expl",
				(main, node, loc, name) -> handleExp(main, node, loc, name, new CPrimitive(CPrimitives.LONGDOUBLE))));

		// see 7.12.6.3 or https://en.cppreference.com/w/c/numeric/math/expm1
		result.add(new FunctionModel("expm1",
				(main, node, loc, name) -> handleExpm1(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("expm1f",
				(main, node, loc, name) -> handleExpm1(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("expm1l",
				(main, node, loc, name) -> handleExpm1(main, node, loc, name, new CPrimitive(CPrimitives.LONGDOUBLE))));

		// see 7.12.8.1 or https://en.cppreference.com/w/c/numeric/math/erf
		result.add(new FunctionModel("erf",
				(main, node, loc, name) -> handleErf(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("erff",
				(main, node, loc, name) -> handleErf(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("erfl",
				(main, node, loc, name) -> handleErf(main, node, loc, name, new CPrimitive(CPrimitives.LONGDOUBLE))));

		// see 7.12.5.6 or https://en.cppreference.com/w/c/numeric/math/tanh
		result.add(new FunctionModel("tanh",
				(main, node, loc, name) -> handleTanh(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("tanhf",
				(main, node, loc, name) -> handleTanh(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("tanhl",
				(main, node, loc, name) -> handleTanh(main, node, loc, name, new CPrimitive(CPrimitives.LONGDOUBLE))));

		// see 7.12.6.7 or https://en.cppreference.com/w/c/numeric/math/log
		result.add(new FunctionModel("log",
				(main, node, loc, name) -> handleLog(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("logf",
				(main, node, loc, name) -> handleLog(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("logl",
				(main, node, loc, name) -> handleLog(main, node, loc, name, new CPrimitive(CPrimitives.LONGDOUBLE))));

		// see 7.12.12.2 or http://en.cppreference.com/w/c/numeric/math/fmax
		result.add(new FunctionModel("fmax",
				(main, node, loc, name) -> handleFmax(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("fmaxf",
				(main, node, loc, name) -> handleFmax(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("fmaxl",
				(main, node, loc, name) -> handleFmax(main, node, loc, name, new CPrimitive(CPrimitives.LONGDOUBLE))));

		// see 7.12.12.3 or http://en.cppreference.com/w/c/numeric/math/fmin
		result.add(new FunctionModel("fmin",
				(main, node, loc, name) -> handleFmin(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("fminf",
				(main, node, loc, name) -> handleFmin(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("fminl",
				(main, node, loc, name) -> handleFmin(main, node, loc, name, new CPrimitive(CPrimitives.LONGDOUBLE))));

		// see 7.12.12.1 or https://en.cppreference.com/w/c/numeric/math/fdim
		result.add(new FunctionModel("fdim",
				(main, node, loc, name) -> handleFdim(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("fdimf",
				(main, node, loc, name) -> handleFdim(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("fdiml",
				(main, node, loc, name) -> handleFdim(main, node, loc, name, new CPrimitive(CPrimitives.LONGDOUBLE))));

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

		// see 7.12.10.2 or http://en.cppreference.com/w/c/numeric/math/remainder
		result.add(new FunctionModel("remainder",
				(main, node, loc, name) -> handleRemainder(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("remainderf",
				(main, node, loc, name) -> handleRemainder(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("remainderl", (main, node, loc, name) -> handleRemainder(main, node, loc, name,
				new CPrimitive(CPrimitives.LONGDOUBLE))));

		/**
		 * 7.12.10.1 The fmod functions
		 *
		 * The fmod functions compute the floating-point remainder of x/y.
		 *
		 * The fmod functions return the value x − ny, for some integer n such that, if y is nonzero, the result has the
		 * same sign as x and magnitude less than the magnitude of y. If y is zero, whether a domain error occurs or the
		 * fmod functions return zero is implementation- defined.
		 */
		// fmod guarantees that the return value is the same sign as the first argument (x)
		result.add(new FunctionModel("fmod",
				(main, node, loc, name) -> handleFmod(main, node, loc, name, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("fmodf",
				(main, node, loc, name) -> handleFmod(main, node, loc, name, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("fmodl",
				(main, node, loc, name) -> handleFmod(main, node, loc, name, new CPrimitive(CPrimitives.LONGDOUBLE))));

		return result;
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return Arrays.asList(UNSUPPORTED_FLOAT_OPERATIONS);
	}

	private ExpressionResult handleNan(final ILocation loc, final CPrimitive type) {
		return new ExpressionResult(new RValue(mFloatHandler.createNan(loc, type), type));
	}

	private ExpressionResult handleInf(final ILocation loc) {
		final CPrimitive type = new CPrimitive(CPrimitives.DOUBLE);
		return new ExpressionResult(new RValue(mFloatHandler.createInfinity(loc, type), type));
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
		final Expression leftExpr = mFloatHandler.isNan(loc, leftRvaluedResult.getLrValue().getValue(),
				(CPrimitive) leftRvaluedResult.getCType());
		final Expression rightExpr = mFloatHandler.isNan(loc, rightRvaluedResult.getLrValue().getValue(),
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
		return new ExpressionResultBuilder()
				.addAllExceptLrValue(argumentResult).setLrValue(new RValue(mExpressionTranslation
						.getFloatingPointHandler().sqrt(loc, argumentResult.getLrValue().getValue(), type), type))
				.build();
	}

	private ExpressionResult handleRound(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type, final Expression roundingMode) {
		final ExpressionResult argumentResult = handleFloatArguments(main, node, loc, name, 1, type).getFirst();
		return new ExpressionResultBuilder().addAllExceptLrValue(argumentResult)
				.setLrValue(new RValue(
						mFloatHandler.roundToIntegral(loc, argumentResult.getLrValue().getValue(), type, roundingMode),
						type))
				.build();
	}

	private ExpressionResult handleRoundWithIntConversion(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type, final CPrimitive resultType,
			final Expression roundingMode) {
		return mExpressionTranslation.convertFloatToInt(loc, handleRound(main, node, loc, name, type, roundingMode),
				resultType);
	}

	private ExpressionResult handleFabs(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final ExpressionResult argumentResult = handleFloatArguments(main, node, loc, name, 1, type).getFirst();
		return new ExpressionResultBuilder()
				.addAllExceptLrValue(argumentResult).setLrValue(new RValue(mExpressionTranslation
						.getFloatingPointHandler().abs(loc, argumentResult.getLrValue().getValue(), type), type))
				.build();
	}

	private ExpressionResult handleIsNan(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);
		final ExpressionResult argumentResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		return new ExpressionResultBuilder().addAllExceptLrValue(argumentResult)
				.setLrValue(new RValue(mFloatHandler.isNan(loc, argumentResult.getLrValue().getValue(),
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
				.setLrValue(new RValue(mFloatHandler.isInfinite(loc, argumentResult.getLrValue().getValue(),
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
		final Expression isInfinite = mFloatHandler.isInfinite(loc, argument, type);
		final Expression isPositive = mFloatHandler.isPositive(loc, argument, type);
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
		final Expression resultExpr = ExpressionFactory.or(loc, mFloatHandler.isNormal(loc, argument, type),
				mFloatHandler.isSubnormal(loc, argument, type), mFloatHandler.isZero(loc, argument, type));
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
		final Expression isInfinite = mFloatHandler.isInfinite(loc, argument, type);
		final Expression isNan = mFloatHandler.isNan(loc, argument, type);
		final Expression isNormal = mFloatHandler.isNormal(loc, argument, type);
		final Expression isSubnormal = mFloatHandler.isSubnormal(loc, argument, type);
		// if (isinf(x)) return FP_INFINITE;
		// else if (isnan(x)) return FP_NAN;
		// else if (isnormal(x)) return FP_NORMAL;
		// else if (issubnormal(x)) return FP_SUBNORMAL;
		// else return FP_ZERO;
		final Expression resultExpr = ExpressionFactory.constructIfThenElseExpression(loc, isInfinite,
				Classification.INFINITE.asExpression(loc, mExpressionTranslation),
				ExpressionFactory.constructIfThenElseExpression(loc, isNan,
						Classification.NAN.asExpression(loc, mExpressionTranslation),
						ExpressionFactory.constructIfThenElseExpression(loc, isNormal,
								Classification.NORMAL.asExpression(loc, mExpressionTranslation),
								ExpressionFactory.constructIfThenElseExpression(loc, isSubnormal,
										Classification.SUBNORMAL.asExpression(loc, mExpressionTranslation),
										Classification.ZERO.asExpression(loc, mExpressionTranslation)))));
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
				.setLrValue(new RValue(mFloatHandler.isNormal(loc, argumentResult.getLrValue().getValue(),
						(CPrimitive) argumentResult.getCType()), new CPrimitive(CPrimitives.INT), true))
				.build();
	}

	private ExpressionResult handleCos(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final ExpressionResult argumentResult = handleFloatArguments(main, node, loc, name, 1, type).getFirst();
		final Expression nan = mFloatHandler.createNan(loc, type);
		final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, type, AUXVAR.RETURNED);
		final Expression one = mExpressionTranslation.constructLiteralForFloatingType(loc, type, BigDecimal.ONE);
		final Expression minusOne =
				mExpressionTranslation.constructLiteralForFloatingType(loc, type, BigDecimal.ONE.negate());
		final Expression greaterMinusOne = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_greaterEqual, auxVar.getExp(), type, minusOne, type);
		final Expression smallerOne = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, auxVar.getExp(), type, one, type);
		// x = 0 ==> cos(x) = 1
		// x = -oo ==> cos(x) = NaN
		// x = oo ==> cos(x) = NaN
		// -1 <= cos(x) <= 1
		return overapproximateUnaryFloatFunction(loc, name, argumentResult, auxVar, nan, nan, one,
				List.of(greaterMinusOne, smallerOne));
	}

	private ExpressionResult handleSin(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final ExpressionResult argumentResult = handleFloatArguments(main, node, loc, name, 1, type).getFirst();
		final Expression nan = mFloatHandler.createNan(loc, type);
		final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, type, AUXVAR.RETURNED);
		final Expression one = mExpressionTranslation.constructLiteralForFloatingType(loc, type, BigDecimal.ONE);
		final Expression minusOne =
				mExpressionTranslation.constructLiteralForFloatingType(loc, type, BigDecimal.ONE.negate());
		final Expression greaterMinusOne = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_greaterEqual, auxVar.getExp(), type, minusOne, type);
		final Expression smallerOne = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, auxVar.getExp(), type, one, type);
		// x = 0 ==> sin(x) = 0
		// x = -oo ==> sin(x) = NaN
		// x = oo ==> sin(x) = NaN
		// -1 <= sin(x) <= 1
		return overapproximateUnaryFloatFunction(loc, name, argumentResult, auxVar, nan, nan,
				argumentResult.getLrValue().getValue(), List.of(greaterMinusOne, smallerOne));
	}

	private ExpressionResult handleExp(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final ExpressionResult argumentResult = handleFloatArguments(main, node, loc, name, 1, type).getFirst();
		final Expression argument = argumentResult.getLrValue().getValue();
		final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, type, AUXVAR.RETURNED);
		final Expression one = mExpressionTranslation.constructLiteralForFloatingType(loc, type, BigDecimal.ONE);
		final Expression positive = mFloatHandler.isPositive(loc, auxVar.getExp(), type);
		final Expression smallerOneForNegativeValues = ExpressionFactory.or(loc,
				mExpressionTranslation.constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_greaterEqual,
						argument, type,
						mExpressionTranslation.constructLiteralForFloatingType(loc, type, BigDecimal.ZERO), type),
				mExpressionTranslation.constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessThan,
						auxVar.getExp(), type, one, type));
		final Expression overLinear = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_greaterEqual, auxVar.getExp(), type, mExpressionTranslation
						.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus, argument, type, one, type),
				type);
		// x = 0 ==> exp(x) = 1
		// x = -oo ==> exp(x) = +0
		// x = oo ==> exp(x) = oo
		// exp(x) >= 0
		// x < 0 ==> exp(x) < 1
		// exp(x) >= x+1
		return overapproximateUnaryFloatFunction(loc, name, argumentResult, auxVar,
				mFloatHandler.createPlusZero(loc, type), argument, one,
				List.of(positive, smallerOneForNegativeValues, overLinear));
	}

	private ExpressionResult handleExpm1(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final ExpressionResult expResult = handleExp(main, node, loc, name, type);
		// expm1(x) = exp(x) - 1
		final Expression resMinusOne = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_minus, expResult.getLrValue().getValue(), type,
				mExpressionTranslation.constructLiteralForFloatingType(loc, type, BigDecimal.ONE), type);
		return new ExpressionResultBuilder(expResult).resetLrValue(new RValue(resMinusOne, type)).build();
	}

	private ExpressionResult handleErf(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final ExpressionResult argumentResult = handleFloatArguments(main, node, loc, name, 1, type).getFirst();
		final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, type, AUXVAR.RETURNED);
		final Expression one = mExpressionTranslation.constructLiteralForFloatingType(loc, type, BigDecimal.ONE);
		final Expression minusOne =
				mExpressionTranslation.constructLiteralForFloatingType(loc, type, BigDecimal.ONE.negate());
		final Expression greaterMinusOne = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_greaterEqual, auxVar.getExp(), type, minusOne, type);
		final Expression smallerOne = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, auxVar.getExp(), type, one, type);
		// x = 0 ==> erf(x) = 0
		// x = -oo ==> erf(x) = -1
		// x = oo ==> erf(x) = 1
		// -1 <= erf(x) <= 1
		return overapproximateUnaryFloatFunction(loc, name, argumentResult, auxVar, minusOne, one,
				argumentResult.getLrValue().getValue(), List.of(greaterMinusOne, smallerOne));
	}

	private ExpressionResult handleTanh(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final ExpressionResult argumentResult = handleFloatArguments(main, node, loc, name, 1, type).getFirst();
		final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, type, AUXVAR.RETURNED);
		final Expression one = mExpressionTranslation.constructLiteralForFloatingType(loc, type, BigDecimal.ONE);
		final Expression minusOne =
				mExpressionTranslation.constructLiteralForFloatingType(loc, type, BigDecimal.ONE.negate());
		final Expression greaterMinusOne = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_greaterEqual, auxVar.getExp(), type, minusOne, type);
		final Expression smallerOne = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, auxVar.getExp(), type, one, type);
		// x = 0 ==> tanh(x) = 0
		// x = -oo ==> tanh(x) = -1
		// x = oo ==> tanh(x) = 1
		// -1 <= tanh(x) <= 1
		return overapproximateUnaryFloatFunction(loc, name, argumentResult, auxVar, minusOne, one,
				argumentResult.getLrValue().getValue(), List.of(greaterMinusOne, smallerOne));
	}

	private ExpressionResult handleLog(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final ExpressionResult argumentResult = handleFloatArguments(main, node, loc, name, 1, type).getFirst();
		final Expression argument = argumentResult.getLrValue().getValue();
		final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, type, AUXVAR.RETURNED);
		final Expression one = mExpressionTranslation.constructLiteralForFloatingType(loc, type, BigDecimal.ONE);
		final Expression nanForNegative = ExpressionFactory.or(loc, mFloatHandler.isPositive(loc, argument, type),
				mFloatHandler.isNan(loc, auxVar.getExp(), type));
		final Expression zeroForOne = ExpressionFactory.or(loc,
				mExpressionTranslation.constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_notequals,
						argument, type, one, type),
				mExpressionTranslation.constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_equals,
						auxVar.getExp(), type, mFloatHandler.createPlusZero(loc, type), type));
		final Expression positiveForGreaterOne = ExpressionFactory.or(loc,
				mExpressionTranslation.constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual,
						argument, type, one, type),
				mExpressionTranslation.constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_greaterThan,
						auxVar.getExp(), type,
						mExpressionTranslation.constructLiteralForFloatingType(loc, type, BigDecimal.ZERO), type));
		final Expression sublinear = ExpressionFactory.or(loc,
				ExpressionFactory.not(loc, mFloatHandler.isPositive(loc, argument, type)),
				mExpressionTranslation.constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual,
						auxVar.getExp(), type, mExpressionTranslation.constructArithmeticExpression(loc,
								IASTBinaryExpression.op_minus, argument, type, one, type),
						type));
		// x = 0 ==> log(x) = -oo
		// x = -oo ==> log(x) = NaN
		// x = oo ==> log(x) = oo
		// x < 0 ==> log(x) = NaN
		// x = 1 ==> log(x) = 0
		// x > 1 ==> log(x) > 0
		// x >= 0 ==> log(x) < x-1
		return overapproximateUnaryFloatFunction(loc, name, argumentResult, auxVar, mFloatHandler.createNan(loc, type),
				argument, mFloatHandler.createMinusInfinity(loc, type),
				List.of(nanForNegative, zeroForOne, positiveForGreaterOne, sublinear));
	}

	private ExpressionResult overapproximateUnaryFloatFunction(final ILocation loc, final String functionName,
			final ExpressionResult argumentResult, final AuxVarInfo auxvarinfo, final Expression negInfValue,
			final Expression posInfValue, final Expression zeroValue,
			final List<Expression> assumptionsForOverapproximation) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder().addAllExceptLrValue(argumentResult);
		builder.addAuxVarWithDeclaration(auxvarinfo);
		final IdentifierExpression auxvar = auxvarinfo.getExp();
		final CPrimitive resultType = (CPrimitive) argumentResult.getCType();
		final Expression argument = argumentResult.getLrValue().getValue();
		builder.setLrValue(new RValue(auxvar, resultType));
		final VariableLHS auxvarLhs = auxvarinfo.getLhs();
		final HavocStatement havoc = new HavocStatement(loc, new VariableLHS[] { auxvarLhs });
		final AssumeStatement assume =
				new AssumeStatement(loc, ExpressionFactory.and(loc, assumptionsForOverapproximation));
		final Statement overapproxSt = new AtomicStatement(loc, new Statement[] { havoc, assume });
		new OverapproxVariable(functionName, loc).annotate(overapproxSt);
		final Expression isZero = mFloatHandler.isZero(loc, argument, resultType);
		final Expression isNan = mFloatHandler.isNan(loc, argument, resultType);
		final Expression isInfinite = mFloatHandler.isInfinite(loc, argument, resultType);
		final Expression isPositive = mFloatHandler.isPositive(loc, argument, resultType);
		final Statement resultStatement =
				StatementFactory.constructIfStatement(loc, isZero,
						List.of(StatementFactory.constructSingleAssignmentStatement(loc, auxvarLhs, zeroValue)),
						List.of(StatementFactory.constructIfStatement(loc, isNan,
								List.of(StatementFactory.constructSingleAssignmentStatement(loc, auxvarLhs, argument)),
								List.of(StatementFactory.constructIfStatement(
										loc, isInfinite, List
												.of(StatementFactory
														.constructSingleAssignmentStatement(loc, auxvarLhs,
																ExpressionFactory.constructIfThenElseExpression(loc,
																		isPositive, posInfValue, negInfValue))),
										List.of(overapproxSt))))));
		return builder.addStatement(resultStatement).build();
	}

	// NaN arguments are treated as missing data: if one argument is a NaN and the other numeric, then the numeric value
	// is choosen.
	private ExpressionResult handleFmin(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final List<ExpressionResult> arguments = handleFloatArguments(main, node, loc, name, 2, type);
		return new ExpressionResultBuilder().addAllExceptLrValue(arguments).setLrValue(new RValue(mFloatHandler.min(loc,
				arguments.get(0).getLrValue().getValue(), arguments.get(1).getLrValue().getValue(), type), type))
				.build();
	}

	// NaN arguments are treated as missing data: if one argument is a NaN and the other numeric, then the numeric value
	// is choosen.
	private ExpressionResult handleFmax(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final List<ExpressionResult> arguments = handleFloatArguments(main, node, loc, name, 2, type);
		return new ExpressionResultBuilder().addAllExceptLrValue(arguments).setLrValue(new RValue(mFloatHandler.max(loc,
				arguments.get(0).getLrValue().getValue(), arguments.get(1).getLrValue().getValue(), type), type))
				.build();
	}

	private ExpressionResult handleFdim(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final List<ExpressionResult> arguments = handleFloatArguments(main, node, loc, name, 2, type);
		final Expression first = arguments.get(0).getLrValue().getValue();
		final Expression second = arguments.get(1).getLrValue().getValue();
		final Expression comparison = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_greaterThan, first, type, second, type);
		final Expression subtraction = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_minus, first, type, second, type);
		final Expression zero = mExpressionTranslation.constructLiteralForFloatingType(loc, type, BigDecimal.ZERO);
		final Expression resultExprFdim =
				ExpressionFactory.constructIfThenElseExpression(loc, comparison, subtraction, zero);
		final Expression secondNaNExpr = ExpressionFactory.constructIfThenElseExpression(loc,
				mFloatHandler.isNan(loc, second, type), second, resultExprFdim);
		final Expression firstNaNExpr = ExpressionFactory.constructIfThenElseExpression(loc,
				mFloatHandler.isNan(loc, first, type), first, secondNaNExpr);
		return new ExpressionResultBuilder().addAllExceptLrValue(arguments).setLrValue(new RValue(firstNaNExpr, type))
				.build();
	}

	private ExpressionResult handleSignbit(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);
		final ExpressionResult argumentResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final CPrimitive intType = new CPrimitive(CPrimitives.INT);
		final Expression argument = argumentResult.getLrValue().getValue();
		final CPrimitive type = (CPrimitive) argumentResult.getCType();
		final ExpressionResultBuilder builder = new ExpressionResultBuilder().addAllExceptLrValue(argumentResult);
		final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, intType, AUXVAR.RETURNED);
		builder.addAuxVarWithDeclaration(auxVar);
		final Statement nondet = new HavocStatement(loc, new VariableLHS[] { auxVar.getLhs() });
		// TODO: Handle negative NaN correctly, only overapproximated until then
		// signbit(x) := isNegative(x) ? 1 : 0;
		new OverapproxVariable("sign of NaN", loc).annotate(nondet);
		final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(loc, intType, BigInteger.ZERO);
		builder.addStatement(StatementFactory.constructIfStatement(loc, mFloatHandler.isNan(loc, argument, type),
				List.of(nondet),
				List.of(StatementFactory.constructIfStatement(loc, mFloatHandler.isPositive(loc, argument, type),
						List.of(StatementFactory.constructSingleAssignmentStatement(loc, auxVar.getLhs(), zero)),
						List.of(new AssumeStatement(loc, ExpressionFactory.newBinaryExpression(loc, Operator.COMPNEQ,
								auxVar.getExp(), zero)))))));
		return builder.setLrValue(new RValue(auxVar.getExp(), intType)).build();
	}

	private ExpressionResult handleCopysign(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final List<ExpressionResult> arguments = handleFloatArguments(main, node, loc, name, 2, type);
		final Expression first = arguments.get(0).getLrValue().getValue();
		final Expression second = arguments.get(1).getLrValue().getValue();
		return new ExpressionResultBuilder().addAllExceptLrValue(arguments)
				.addAllIncludingLrValue(handleCopysign(first, second, loc, type)).build();
	}

	private ExpressionResult handleCopysign(final Expression first, final Expression second, final ILocation loc,
			final CPrimitive type) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, type, AUXVAR.RETURNED);
		builder.addAuxVarWithDeclaration(auxVar);
		final Expression abs = mFloatHandler.abs(loc, first, type);
		final Statement nondet = new AssumeStatement(loc,
				ExpressionFactory.or(loc,
						mExpressionTranslation.constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_equals,
								auxVar.getExp(), type, first, type),
						mExpressionTranslation.constructBinaryComparisonExpression(
								loc, IASTBinaryExpression.op_equals, auxVar.getExp(), type, mExpressionTranslation
										.constructUnaryExpression(loc, IASTUnaryExpression.op_minus, first, type),
								type)));
		// TODO: Overapproximate if second is NaN
		new OverapproxVariable("sign of NaN", loc).annotate(nondet);
		builder.addStatement(StatementFactory.constructIfStatement(loc, mFloatHandler.isNan(loc, first, type),
				// If the first argument is NaN, just return it. This works for now, as we cannot handle negative NaN
				// anyway.
				// TODO: If we can handle negative NaN, this has to be changed!
				List.of(StatementFactory.constructSingleAssignmentStatement(loc, auxVar.getLhs(), first)),
				List.of(StatementFactory.constructIfStatement(loc, mFloatHandler.isNan(loc, second, type),
						List.of(nondet),
						List.of(StatementFactory.constructSingleAssignmentStatement(loc, auxVar.getLhs(),
								ExpressionFactory.constructIfThenElseExpression(loc,
										mFloatHandler.isPositive(loc, second, type), abs,
										mExpressionTranslation.constructUnaryExpression(loc,
												IASTUnaryExpression.op_minus, abs, type))))))));
		return builder.setLrValue(new RValue(auxVar.getExp(), type)).build();
	}

	private ExpressionResult handleRemainder(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final List<ExpressionResult> arguments = handleFloatArguments(main, node, loc, name, 2, type);
		final Expression first = arguments.get(0).getLrValue().getValue();
		final Expression second = arguments.get(1).getLrValue().getValue();
		return new ExpressionResultBuilder().addAllExceptLrValue(arguments)
				.setLrValue(new RValue(mFloatHandler.remainder(loc, first, second, type), type)).build();
	}

	private ExpressionResult handleFmod(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final CPrimitive type) {
		final List<ExpressionResult> arguments = handleFloatArguments(main, node, loc, name, 2, type);
		final Expression first = arguments.get(0).getLrValue().getValue();
		final Expression second = arguments.get(1).getLrValue().getValue();
		// fmod(x, y) {
		// r = remainder(fabs(x), fabs(y));
		// pr = isPositive(r) ? r : r + fabs(y);
		// return copysign(pr, x)
		// }
		final Expression remainder = mFloatHandler.remainder(loc, mFloatHandler.abs(loc, first, type),
				mFloatHandler.abs(loc, second, type), type);
		final Expression positiveRemainder = ExpressionFactory.constructIfThenElseExpression(loc,
				mFloatHandler.isPositive(loc, remainder, type), remainder,
				mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus, remainder, type,
						mFloatHandler.abs(loc, second, type), type));
		return new ExpressionResultBuilder().addAllExceptLrValue(arguments)
				.addAllIncludingLrValue(handleCopysign(positiveRemainder, first, loc, type)).build();
	}

	@Override
	public Collection<TypeModel> getTypeModels() {
		return List.of(
				// most efficient floating-point type at least as wide as float -> We choose float
				new TypeModel("float_t", new CPrimitive(CPrimitives.FLOAT)),
				// most efficient floating-point type at least as wide as double -> We choose double
				new TypeModel("double_t", new CPrimitive(CPrimitives.DOUBLE)));
	}

	@Override
	public Collection<ConstantModel> getConstantModels() {
		final List<ConstantModel> result = new ArrayList<>();
		result.add(new ConstantModel("NAN", loc -> handleNan(loc, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new ConstantModel("INFINITY", loc -> handleInf(loc)));
		result.add(new ConstantModel("inf", loc -> handleInf(loc)));
		for (final Classification c : Classification.values()) {
			result.add(new ConstantModel(c.getName(), loc -> new ExpressionResult(
					new RValue(c.asExpression(loc, mExpressionTranslation), new CPrimitive(CPrimitives.INT)))));
		}
		return result;
	}
}
