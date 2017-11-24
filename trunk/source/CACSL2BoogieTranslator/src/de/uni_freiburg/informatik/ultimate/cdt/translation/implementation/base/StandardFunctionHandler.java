/*
 * Copyright (C) 2013-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.FunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.LocalLValueILocationPair;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.FloatFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.FloatSupportInUltimate;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LTLStepAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerCheckMode;

/**
 * The {@link StandardFunctionHandler} creates the translation for various functions where we have our own specification
 * or implementation. This is typically the case for functions defined in the C standard, but also for various standard
 * libraries or SV-COMP extensions.
 *
 * @author Markus Lindenmann,
 * @auhtor Matthias Heizmann
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class StandardFunctionHandler {

	private final Map<String, IFunctionModelHandler> mFunctionModels;

	private final ITypeHandler mTypeHandler;

	private final ExpressionTranslation mExpressionTranslation;

	private final MemoryHandler mMemoryHandler;

	private final StructHandler mStructHandler;

	private final TypeSizeAndOffsetComputer mTypeSizeComputer;

	private final FunctionHandler mFunctionHandler;

	private final CHandler mCHandler;

	public StandardFunctionHandler(final ITypeHandler typeHandler, final ExpressionTranslation expressionTranslation,
			final MemoryHandler memoryHandler, final StructHandler structHandler,
			final TypeSizeAndOffsetComputer typeSizeComputer, final FunctionHandler functionHandler,
			final CHandler cHandler) {
		mTypeHandler = typeHandler;
		mExpressionTranslation = expressionTranslation;
		mMemoryHandler = memoryHandler;
		mStructHandler = structHandler;
		mTypeSizeComputer = typeSizeComputer;
		mFunctionHandler = functionHandler;
		mCHandler = cHandler;

		mFunctionModels = getFunctionModels();
	}

	/**
	 * Check if the given function has an "integrated" specification or implementation and return a {@link Result} that
	 * contains a translation of the function if this is the case.
	 *
	 * Return null otherwise.
	 *
	 * @param main
	 * @param node
	 * @param astIdExpression
	 * @return
	 */
	public Result translateStandardFunction(final Dispatcher main, final IASTFunctionCallExpression node,
			final IASTIdExpression astIdExpression) {
		assert node
				.getFunctionNameExpression() == astIdExpression : "astIdExpression is not the name of the called function";
		final String name = astIdExpression.getName().toString();
		final IFunctionModelHandler functionModel = mFunctionModels.get(name);
		if (functionModel != null) {
			final IASTNode funDecl = main.getFunctionTable().get(name);
			if (funDecl instanceof IASTFunctionDefinition) {
				// it is a function that already has a body
				return null;
			}
			final ILocation loc = getLoc(main, node);
			return functionModel.handleFunction(main, node, loc, name);
		}
		return null;
	}

	private Map<String, IFunctionModelHandler> getFunctionModels() {
		final Map<String, IFunctionModelHandler> map = new HashMap<>();

		final IFunctionModelHandler skip = (main, node, loc, name) -> handleByIgnore(main, loc, name);
		final IFunctionModelHandler die = (main, node, loc, name) -> handleByUnsupportedSyntaxException(loc, name);
		final IFunctionModelHandler dieFloat =
				(main, node, loc, name) -> handleByUnsupportedSyntaxExceptionKnown(loc, "math.h", name);

		for (final String unsupportedFloatFunction : FloatSupportInUltimate.getUnsupportedFloatOperations()) {
			fill(map, unsupportedFloatFunction, dieFloat);
		}

		fill(map, "pthread_create", die);

		fill(map, "abort", (main, node, loc, name) -> handleAbort(loc));

		fill(map, "printf", (main, node, loc, name) -> handlePrintF(main, node, loc));

		fill(map, "__builtin_memcpy", this::handleMemCopy);
		fill(map, "memcpy", this::handleMemCopy);

		fill(map, "malloc", this::handleAlloc);
		fill(map, "alloca", this::handleAlloc);
		fill(map, "__builtin_alloca", this::handleAlloc);
		fill(map, "calloc", this::handleCalloc);
		fill(map, "memset", this::handleMemset);
		fill(map, "free", this::handleFree);

		/*
		 * The GNU C online documentation at https://gcc.gnu.org/onlinedocs/gcc/Return-Address.html on 09 Nov 2016 says:
		 * "— Built-in Function: void * __builtin_return_address (unsigned int level) This function returns the return
		 * address of the current function, or of one of its callers. The level argument is number of frames to scan up
		 * the call stack. A value of 0 yields the return address of the current function, a value of 1 yields the
		 * return address of the caller of the current function, and so forth. When inlining the expected behavior is
		 * that the function returns the address of the function that is returned to. To work around this behavior use
		 * the noinline function attribute.
		 *
		 * The level argument must be a constant integer. On some machines it may be impossible to determine the return
		 * address of any function other than the current one; in such cases, or when the top of the stack has been
		 * reached, this function returns 0 or a random value. In addition, __builtin_frame_address may be used to
		 * determine if the top of the stack has been reached. Additional post-processing of the returned value may be
		 * needed, see __builtin_extract_return_addr. Calling this function with a nonzero argument can have
		 * unpredictable effects, including crashing the calling program. As a result, calls that are considered unsafe
		 * are diagnosed when the -Wframe-address option is in effect. Such calls should only be made in debugging
		 * situations."
		 *
		 * Current solution: replace call by a havocced aux variable.
		 */
		fill(map, "__builtin_return_address", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 1, new CPointer(new CPrimitive(CPrimitives.VOID))));

		fill(map, "__builtin_bswap32", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.UINT)));
		fill(map, "__builtin_bswap64", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.ULONG)));

		/*
		 * builtin_prefetch according to https://gcc.gnu.org/onlinedocs/gcc-3.4.5/gcc/Other-Builtins.html (state:
		 * 5.6.2015) triggers the processor to load something into cache, does nothing else is void thus has no return
		 * value
		 */
		fill(map, "__builtin_prefetch", skip);
		fill(map, "__builtin_va_start", skip);
		fill(map, "__builtin_va_end", skip);

		fill(map, "__builtin_expect", this::handleBuiltinExpect);
		fill(map, "__builtin_unreachable", (main, node, loc, name) -> handleBuiltinUnreachable(loc));
		fill(map, "__builtin_object_size", (main, node, loc, name) -> handleBuiltinObjectSize(main, loc));

		/** various string builtins **/
		fill(map, "__builtin_strchr", this::handleStrChr);
		fill(map, "strchr", this::handleStrChr);
		fill(map, "__builtin_strlen", this::handleStrLen);
		fill(map, "strlen", this::handleStrLen);
		fill(map, "__builtin_strcmp", this::handleStrCmp);
		fill(map, "strcmp", this::handleStrCmp);

		/** various float builtins **/
		fill(map, "nan", (main, node, loc, name) -> handleNaNOrInfinity(loc, name));
		fill(map, "nanf", (main, node, loc, name) -> handleNaNOrInfinity(loc, name));
		fill(map, "nanl", (main, node, loc, name) -> handleNaNOrInfinity(loc, name));
		fill(map, "__builtin_nan", (main, node, loc, name) -> handleNaNOrInfinity(loc, "nan"));
		fill(map, "__builtin_nanf", (main, node, loc, name) -> handleNaNOrInfinity(loc, "nanf"));
		fill(map, "__builtin_nanl", (main, node, loc, name) -> handleNaNOrInfinity(loc, "nanl"));
		fill(map, "__builtin_inff", (main, node, loc, name) -> handleNaNOrInfinity(loc, "inff"));
		fill(map, "__builtin_huge_val", (main, node, loc, name) -> handleNaNOrInfinity(loc, "inf"));
		fill(map, "__builtin_huge_valf", (main, node, loc, name) -> handleNaNOrInfinity(loc, "inff"));
		fill(map, "__builtin_isgreater", (main, node, loc, name) -> handleFloatBuiltinBinaryComparison(main, node, loc,
				name, IASTBinaryExpression.op_greaterThan));
		fill(map, "__builtin_isgreaterequal", (main, node, loc, name) -> handleFloatBuiltinBinaryComparison(main, node,
				loc, name, IASTBinaryExpression.op_greaterEqual));
		fill(map, "__builtin_isless", (main, node, loc, name) -> handleFloatBuiltinBinaryComparison(main, node, loc,
				name, IASTBinaryExpression.op_lessThan));
		fill(map, "__builtin_islessequal", (main, node, loc, name) -> handleFloatBuiltinBinaryComparison(main, node,
				loc, name, IASTBinaryExpression.op_lessEqual));
		fill(map, "__builtin_isunordered", this::handleFloatBuiltinIsUnordered);
		fill(map, "__builtin_islessgreater", this::handleFloatBuiltinIsLessGreater);

		/** math.h float functions **/
		// see 7.12.3.1 or http://en.cppreference.com/w/c/numeric/math/fpclassify
		fill(map, "fpclassify", this::handleUnaryFloatFunction);
		fill(map, "__fpclassify", this::handleUnaryFloatFunction); // ??
		fill(map, "__fpclassifyf", this::handleUnaryFloatFunction); // ??
		fill(map, "__fpclassifyl", this::handleUnaryFloatFunction); // ??

		// see 7.12.3.2 or http://en.cppreference.com/w/c/numeric/math/isfinite
		fill(map, "isfinite", this::handleUnaryFloatFunction);

		// see https://linux.die.net/man/3/finite (! NOT PART OF ANSI-C)
		fill(map, "finite", this::handleUnaryFloatFunction);
		fill(map, "__finite", this::handleUnaryFloatFunction);
		fill(map, "finitef", this::handleUnaryFloatFunction);
		fill(map, "__finitef", this::handleUnaryFloatFunction); // ??
		fill(map, "finitel", this::handleUnaryFloatFunction);
		fill(map, "__finitel", this::handleUnaryFloatFunction); // ??

		// see 7.12.3.3 or http://en.cppreference.com/w/c/numeric/math/isinf
		fill(map, "isinf", this::handleUnaryFloatFunction);
		fill(map, "__isinf", this::handleUnaryFloatFunction); // ??
		// see https://linux.die.net/man/3/finite (! NOT PART OF ANSI-C)
		fill(map, "isinff", this::handleUnaryFloatFunction);
		fill(map, "__isinff", this::handleUnaryFloatFunction); // ??
		fill(map, "isinfl", this::handleUnaryFloatFunction);
		fill(map, "__isinfl", this::handleUnaryFloatFunction); // ??

		// see 7.12.3.4 or http://en.cppreference.com/w/c/numeric/math/isnan
		fill(map, "isnan", this::handleUnaryFloatFunction);
		fill(map, "__isnan", this::handleUnaryFloatFunction); // ??
		// see https://linux.die.net/man/3/finite (! NOT PART OF ANSI-C)
		fill(map, "isnanf", this::handleUnaryFloatFunction);
		fill(map, "isnanl", this::handleUnaryFloatFunction);
		fill(map, "__isnanf", this::handleUnaryFloatFunction); // ??
		fill(map, "__isnanl", this::handleUnaryFloatFunction); // ??

		// see 7.12.3.5 or http://en.cppreference.com/w/c/numeric/math/isnormal
		fill(map, "isnormal", this::handleUnaryFloatFunction);

		// see 7.12.3.6 or http://en.cppreference.com/w/c/numeric/math/signbit
		fill(map, "signbit", this::handleUnaryFloatFunction);
		fill(map, "__signbit", this::handleUnaryFloatFunction); // ??
		fill(map, "__signbitl", this::handleUnaryFloatFunction); // ??
		fill(map, "__signbitf", this::handleUnaryFloatFunction); // ??

		// see 7.12.7.5 or http://en.cppreference.com/w/c/numeric/math/sqrt
		fill(map, "sqrt", this::handleUnaryFloatFunction);
		fill(map, "sqrtf", this::handleUnaryFloatFunction);
		fill(map, "sqrtl", this::handleUnaryFloatFunction);

		// see 7.12.7.2 or http://en.cppreference.com/w/c/numeric/math/fabs
		fill(map, "fabs", this::handleUnaryFloatFunction);
		fill(map, "fabsf", this::handleUnaryFloatFunction);
		fill(map, "fabsl", this::handleUnaryFloatFunction);

		// see 7.12.12.2 or http://en.cppreference.com/w/c/numeric/math/fmax
		// NaN arguments are treated as missing data: if one argument is a NaN and the other numeric, then the
		// fmin/fmax functions choose the numeric value.
		fill(map, "fmax", this::handleBinaryFloatFunction);
		fill(map, "fmaxf", this::handleBinaryFloatFunction);
		fill(map, "fmaxl", this::handleBinaryFloatFunction);

		// see 7.12.12.3 or http://en.cppreference.com/w/c/numeric/math/fmin
		fill(map, "fmin", this::handleBinaryFloatFunction);
		fill(map, "fminf", this::handleBinaryFloatFunction);
		fill(map, "fminl", this::handleBinaryFloatFunction);

		/** SV-COMP and modelling functions **/
		fill(map, "__VERIFIER_ltl_step", (main, node, loc, name) -> handleLtlStep(main, node, loc));
		fill(map, "__VERIFIER_error", (main, node, loc, name) -> handleErrorFunction(main, node, loc));
		fill(map, "__VERIFIER_assume", this::handleVerifierAssume);

		fill(map, "__VERIFIER_nondet_bool",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.BOOL)));
		fill(map, "__VERIFIER_nondet__Bool",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.BOOL)));
		fill(map, "__VERIFIER_nondet_char",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.CHAR)));
		fill(map, "__VERIFIER_nondet_pchar",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.CHAR)));
		fill(map, "__VERIFIER_nondet_float",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.FLOAT)));
		fill(map, "__VERIFIER_nondet_double",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.DOUBLE)));
		fill(map, "__VERIFIER_nondet_size_t",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.INT)));
		fill(map, "__VERIFIER_nondet_int",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.INT)));
		fill(map, "__VERIFIER_nondet_long",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.LONG)));
		fill(map, "__VERIFIER_nondet_loff_t",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.LONG)));
		fill(map, "__VERIFIER_nondet_short",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.SHORT)));
		fill(map, "__VERIFIER_nondet_pointer", (main, node, loc, name) -> handleVerifierNonDet(main, loc,
				new CPointer(new CPrimitive(CPrimitives.VOID))));
		fill(map, "__VERIFIER_nondet_uchar",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UCHAR)));
		fill(map, "__VERIFIER_nondet_unsigned",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UINT)));
		fill(map, "__VERIFIER_nondet_uint",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.UINT)));
		fill(map, "__VERIFIER_nondet_ulong",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.ULONG)));
		fill(map, "__VERIFIER_nondet_ushort",
				(main, node, loc, name) -> handleVerifierNonDet(main, loc, new CPrimitive(CPrimitives.USHORT)));

		checkFloatSupport(map, dieFloat);

		return Collections.unmodifiableMap(map);
	}

	private static void checkFloatSupport(final Map<String, IFunctionModelHandler> map,
			final IFunctionModelHandler dieFloat) {

		final List<String> declUnSupp = new ArrayList<>();
		final List<String> declNotSupp = new ArrayList<>();
		for (final String supportedFloatFunction : FloatSupportInUltimate.getSupportedFloatOperations()) {
			final IFunctionModelHandler fun = map.get(supportedFloatFunction);
			if (fun == dieFloat) {
				declUnSupp.add(supportedFloatFunction);
				continue;
			}
			if (fun == null) {
				declNotSupp.add(supportedFloatFunction);
				continue;
			}
		}

		if (!declUnSupp.isEmpty()) {
			throw new IllegalStateException("A supported float function is declared as unsupported: " + declUnSupp);
		}
		if (!declNotSupp.isEmpty()) {
			throw new IllegalStateException("A supported float function is not declared: " + declNotSupp);
		}
	}

	private Result handleStrCmp(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult arg0 = dispatchAndConvert(main, loc, arguments[0]);
		builder.addDeclarations(arg0.mDecl);
		builder.addStatements(arg0.mStmt);
		builder.addOverapprox(arg0.mOverappr);
		builder.putAuxVars(arg0.mAuxVars);
		builder.addNeighbourUnionFields(arg0.mOtherUnionFields);

		builder.addStatements(constructMemsafetyChecksForPointerExpression(loc, arg0.mLrVal.getValue(), mMemoryHandler,
				mExpressionTranslation));

		final ExpressionResult arg1 = dispatchAndConvert(main, loc, arguments[1]);
		builder.addDeclarations(arg1.mDecl);
		builder.addStatements(arg1.mStmt);
		builder.addOverapprox(arg1.mOverappr);
		builder.putAuxVars(arg1.mAuxVars);
		builder.addNeighbourUnionFields(arg1.mOtherUnionFields);

		builder.addStatements(constructMemsafetyChecksForPointerExpression(loc, arg1.mLrVal.getValue(), mMemoryHandler,
				mExpressionTranslation));

		final CPrimitive resultType = new CPrimitive(CPrimitives.INT);
		// introduce fresh aux variable
		final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, resultType);
		final VariableDeclaration tmpVarDecl =
				SFO.getTempVarVariableDeclaration(tmpId, main.mTypeHandler.cType2AstType(loc, resultType), loc);
		builder.addDeclaration(tmpVarDecl);
		builder.putAuxVar(tmpVarDecl, loc);

		final IdentifierExpression tmpVarIdExpr = new IdentifierExpression(loc, tmpId);
		final Overapprox overAppFlag = new Overapprox(name, loc);
		builder.addOverapprox(overAppFlag);
		final RValue lrVal = new RValue(tmpVarIdExpr, resultType);
		builder.setLRVal(lrVal);
		return builder.build();
	}

	private Result handleStrLen(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String methodName) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, methodName, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();

		final ExpressionResult arg = dispatchAndConvert(main, loc, arguments[0]);
		builder.addDeclarations(arg.mDecl);
		builder.addStatements(arg.mStmt);
		builder.addOverapprox(arg.mOverappr);
		builder.putAuxVars(arg.mAuxVars);
		builder.addNeighbourUnionFields(arg.mOtherUnionFields);

		builder.addStatements(constructMemsafetyChecksForPointerExpression(loc, arg.mLrVal.getValue(), mMemoryHandler,
				mExpressionTranslation));

		// according to standard result is size_t, we use int for efficiency
		final CPrimitive resultType = new CPrimitive(CPrimitives.INT);
		// introduce fresh aux variable
		final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, resultType);
		final VariableDeclaration tmpVarDecl =
				SFO.getTempVarVariableDeclaration(tmpId, main.mTypeHandler.cType2AstType(loc, resultType), loc);
		builder.addDeclaration(tmpVarDecl);
		builder.putAuxVar(tmpVarDecl, loc);

		final IdentifierExpression tmpVarIdExpr = new IdentifierExpression(loc, tmpId);
		final Overapprox overAppFlag = new Overapprox(methodName, loc);
		builder.addOverapprox(overAppFlag);
		final RValue lrVal = new RValue(tmpVarIdExpr, resultType);
		builder.setLRVal(lrVal);
		return builder.build();
	}

	private Result handleStrChr(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		/*
		 * C11, 7.21.5.2 says: "#include <string.h> char *strchr(const char *s, int c); Description: The strchr function
		 * locates the first occurrence of c (converted to a char) in the string pointed to by s. The terminating null
		 * character is considered to be part of the string. Returns : The strchr function returns a pointer to the
		 * located character, or a null pointer if the character does not occur in the string."
		 *
		 * We replace the method call by a fresh char pointer variable which is havocced, and assumed to be either NULL
		 * or a pointer into the area where the argument pointer is valid.
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		// dispatch first argument -- we need its value for the assume

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult argS = dispatchAndConvert(main, loc, arguments[0]);
		builder.addDeclarations(argS.mDecl).addStatements(argS.mStmt).addOverapprox(argS.mOverappr)
				.putAuxVars(argS.mAuxVars).addNeighbourUnionFields(argS.mOtherUnionFields);

		// dispatch second argument -- only for its sideeffects
		final ExpressionResult argC = dispatchAndConvert(main, loc, arguments[1]);
		builder.addDeclarations(argC.mDecl).addStatements(argC.mStmt).addOverapprox(argC.mOverappr)
				.putAuxVars(argC.mAuxVars).addNeighbourUnionFields(argC.mOtherUnionFields);

		// introduce fresh aux variable
		final CPointer resultType = new CPointer(new CPrimitive(CPrimitives.CHAR));
		final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, resultType);
		final VariableDeclaration tmpVarDecl =
				SFO.getTempVarVariableDeclaration(tmpId, main.mTypeHandler.constructPointerType(loc), loc);
		builder.addDeclaration(tmpVarDecl);
		builder.putAuxVar(tmpVarDecl, loc);

		final Expression nullExpr = mExpressionTranslation.constructNullPointer(loc);

		/*
		 * if we are in memsafety-mode: add assertions that check that arg_s.lrVal.getValue is a valid pointer
		 *
		 * technical Notes: these assertions are added before the assume statement and before the result can be assigned
		 * thus the overapproximation introduced does not affect violations of these assertions
		 */
		builder.addStatements(constructMemsafetyChecksForPointerExpression(loc, argS.mLrVal.getValue(), mMemoryHandler,
				mExpressionTranslation));

		// the havocced/uninitialized variable that represents the return value
		final Expression tmpExpr = new IdentifierExpression(loc, tmpId);

		/*
		 * build the assume statement as described above
		 */
		{
			// res.base == 0 && res.offset == 0
			final Expression baseEqualsNull = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_equals, MemoryHandler.getPointerBaseAddress(tmpExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents(),
					MemoryHandler.getPointerBaseAddress(nullExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents());
			final Expression offsetEqualsNull = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_equals, MemoryHandler.getPointerOffset(tmpExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents(), MemoryHandler.getPointerOffset(nullExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents());
			final BinaryExpression equalsNull =
					new BinaryExpression(loc, Operator.LOGICAND, baseEqualsNull, offsetEqualsNull);
			// old solution did not work quickly..
			// final BinaryExpression equalsNull = expressionTranslation.constructBinaryComparisonExpression(loc,
			// new BinaryExpression(loc, Operator.COMPEQ, tmpExpr, nullExpr);
			// res.base == arg_s.base
			final Expression baseEquals = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_equals, MemoryHandler.getPointerBaseAddress(tmpExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents(),
					MemoryHandler.getPointerBaseAddress(argS.mLrVal.getValue(), loc),
					mExpressionTranslation.getCTypeOfPointerComponents());
			// res.offset >= 0
			final Expression offsetNonNegative = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_lessEqual,
					mExpressionTranslation.constructLiteralForIntegerType(loc,
							mExpressionTranslation.getCTypeOfPointerComponents(), new BigInteger("0")),
					mExpressionTranslation.getCTypeOfPointerComponents(), MemoryHandler.getPointerOffset(tmpExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents());
			// res.offset < length(arg_s.base)
			final Expression offsetSmallerLength = mExpressionTranslation.constructBinaryComparisonIntegerExpression(
					loc, IASTBinaryExpression.op_lessEqual, MemoryHandler.getPointerOffset(tmpExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents(),
					ExpressionFactory.constructNestedArrayAccessExpression(loc, mMemoryHandler.getLengthArray(loc),
							new Expression[] { MemoryHandler.getPointerBaseAddress(argS.mLrVal.getValue(), loc) }),
					mExpressionTranslation.getCTypeOfPointerComponents());
			// res.base == arg_s.base && res.offset >= 0 && res.offset <= length(arg_s.base)
			final BinaryExpression inRange = new BinaryExpression(loc, Operator.LOGICAND, baseEquals,
					new BinaryExpression(loc, Operator.LOGICAND, offsetNonNegative, offsetSmallerLength));
			// assume equalsNull or inRange
			final AssumeStatement assume =
					new AssumeStatement(loc, new BinaryExpression(loc, Operator.LOGICOR, equalsNull, inRange));
			builder.addStatement(assume);
		}

		// final List<Overapprox> overapprox = new ArrayList<>();
		final Overapprox overappFlag = new Overapprox(name, loc);
		// overapprox.add(overappFlag);
		// assume.getPayload().getAnnotations().put(Overapprox.getIdentifier(), overappFlag);
		builder.addOverapprox(overappFlag);

		final RValue lrVal = new RValue(tmpExpr, resultType);
		builder.setLRVal(lrVal);

		return builder.build();
	}

	private static Result handleBuiltinUnreachable(final ILocation loc) {
		// TODO: Add option that allows us to check for builtin_unreachable by adding assert
		// return new ExpressionResult(Collections.singletonList(new AssertStatement(loc,
		// new de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral(loc, false))), null);
		// TODO: Add option that just ignores the function:
		// return new SkipResult();
		// TODO: Keep the following code, but add it as option together with the other two
		return new ExpressionResult(Collections.singletonList(new AssumeStatement(loc, new BooleanLiteral(loc, false))),
				null);
	}

	private Result handleMemset(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		/*
		 * C11 says in 7.24.6.1 void *memset(void *s, int c, size_t n); The memset function copies the value of c
		 * (converted to an unsigned char) into each of the first n characters of the object pointed to by s.
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 3, name, arguments);

		final ExpressionResult argS = dispatchAndConvert(main, loc, arguments[0]);
		final ExpressionResult argC = dispatchAndConvert(main, loc, arguments[1]);
		mExpressionTranslation.convertIntToInt(loc, argC, new CPrimitive(CPrimitives.INT));
		final ExpressionResult argN = dispatchAndConvert(main, loc, arguments[2]);
		mExpressionTranslation.convertIntToInt(loc, argN, mTypeSizeComputer.getSizeT());

		final ExpressionResult result = new ExpressionResult(argS.mLrVal);
		result.addAll(argS);
		result.addAll(argC);
		result.addAll(argN);

		final String tId =
				main.mNameHandler.getTempVarUID(SFO.AUXVAR.MEMSETRES, new CPointer(new CPrimitive(CPrimitives.VOID)));
		final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0],
				new VarList[] { new VarList(loc, new String[] { tId }, main.mTypeHandler.constructPointerType(loc)) });
		result.mDecl.add(tVarDecl);
		result.mAuxVars.put(tVarDecl, loc);

		result.mStmt.add(mMemoryHandler.constructUltimateMemsetCall(loc, argS.mLrVal.getValue(), argC.mLrVal.getValue(),
				argN.mLrVal.getValue(), tId));

		mFunctionHandler.addMemoryModelDeclarations(MemoryModelDeclarations.C_Memset);
		return result;
	}

	private Result handleCalloc(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		/*
		 * C11 says in 7.22.3.2 void *calloc(size_t nmemb, size_t size); The calloc function allocates space for an
		 * array of nmemb objects, each of whose size is size. The space is initialized to all bits zero.
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);

		final ExpressionResult nmemb = dispatchAndConvert(main, loc, arguments[0]);
		main.mCHandler.convert(loc, nmemb, mTypeSizeComputer.getSizeT());
		final ExpressionResult size = dispatchAndConvert(main, loc, arguments[1]);
		main.mCHandler.convert(loc, size, mTypeSizeComputer.getSizeT());

		final Expression product = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_multiply, nmemb.mLrVal.getValue(), mTypeSizeComputer.getSizeT(),
				size.mLrVal.getValue(), mTypeSizeComputer.getSizeT());
		final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(nmemb, size);

		final CPointer resultType = new CPointer(new CPrimitive(CPrimitives.VOID));
		final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.MALLOC, resultType);
		final VariableDeclaration tmpVarDecl =
				SFO.getTempVarVariableDeclaration(tmpId, main.mTypeHandler.constructPointerType(loc), loc);
		result.mDecl.add(tmpVarDecl);

		result.mStmt.add(mMemoryHandler.getMallocCall(product, tmpId, loc));
		result.mLrVal = new RValue(new IdentifierExpression(loc, tmpId), resultType);

		result.mStmt.add(mMemoryHandler.constructUltimateMeminitCall(loc, nmemb.mLrVal.getValue(),
				size.mLrVal.getValue(), product, new IdentifierExpression(loc, tmpId)));

		mFunctionHandler.addMemoryModelDeclarations(MemoryModelDeclarations.Ultimate_MemInit,
				MemoryModelDeclarations.Ultimate_Alloc);
		return result;
	}

	private Result handleFree(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);

		final ExpressionResult pRex = dispatchAndConvert(main, loc, arguments[0]);
		pRex.mStmt.add(getFreeCall(main, pRex.mLrVal, loc));
		return pRex;
	}

	private Result handleAlloc(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String methodName) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, methodName, arguments);

		final ExpressionResult exprRes = dispatchAndConvert(main, loc, arguments[0]);
		main.mCHandler.convert(loc, exprRes, mTypeSizeComputer.getSizeT());

		final CPointer resultType = new CPointer(new CPrimitive(CPrimitives.VOID));
		final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.MALLOC, resultType);
		final VariableDeclaration tmpVarDecl =
				SFO.getTempVarVariableDeclaration(tmpId, main.mTypeHandler.constructPointerType(loc), loc);
		exprRes.mDecl.add(tmpVarDecl);

		exprRes.mStmt.add(mMemoryHandler.getMallocCall(exprRes.mLrVal.getValue(), tmpId, loc));
		exprRes.mLrVal = new RValue(new IdentifierExpression(loc, tmpId), resultType);

		// for alloc a we have to free the variable ourselves when the
		// stackframe is closed, i.e. at a return
		if ("alloca".equals(methodName) || "__builtin_alloca".equals(methodName)) {
			final LocalLValue llVal = new LocalLValue(new VariableLHS(loc, tmpId), resultType);
			mMemoryHandler.addVariableToBeFreed(main,
					new LocalLValueILocationPair(llVal, LocationFactory.createIgnoreLocation(loc)));
			// we need to clear auxVars because otherwise the malloc auxvar is havocced after
			// this, and free (triggered by the statement before) would fail.
			exprRes.mAuxVars.clear();
		}
		return exprRes;
	}

	/**
	 * Construct an auxiliary variable that will be use as a substitute for a function call. The result will be marked
	 * as an overapproximation. If you overapproximate a function call, don't forget to dispatch the function call's
	 * arguments: the arguments may have side effects.
	 *
	 * @param functionName
	 *            the named of the function will be annotated to the overapproximation
	 * @param resultType
	 *            CType that determinies the type of the auxiliary variable
	 */
	private static ExpressionResult constructOverapproximationForFunctionCall(final Dispatcher main,
			final ILocation loc, final String functionName, final CType resultType) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		// introduce fresh aux variable
		final String tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, resultType);
		final ASTType astType = main.mTypeHandler.cType2AstType(loc, resultType);
		final VariableDeclaration tmpVarDecl = SFO.getTempVarVariableDeclaration(tmpId, astType, loc);
		builder.addDeclaration(tmpVarDecl);
		builder.putAuxVar(tmpVarDecl, loc);
		final IdentifierExpression tmpVarIdExpr = new IdentifierExpression(loc, tmpId);
		builder.addOverapprox(new Overapprox(functionName, loc));
		builder.setLRVal(new RValue(tmpVarIdExpr, resultType));
		return builder.build();
	}

	private Result handleBuiltinExpect(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		/**
		 * Built-in Function: long __builtin_expect (long exp, long c)
		 *
		 * You may use __builtin_expect to provide the compiler with branch prediction information. In general, you
		 * should prefer to use actual profile feedback for this (-fprofile-arcs), as programmers are notoriously bad at
		 * predicting how their programs actually perform. However, there are applications in which this data is hard to
		 * collect.
		 *
		 * The return value is the value of exp, which should be an integral expression. The semantics of the built-in
		 * are that it is expected that exp == c. For example:
		 *
		 * <code>if (__builtin_expect (x, 0)) foo ();</code>
		 *
		 * indicates that we do not expect to call foo, since we expect x to be zero. Since you are limited to integral
		 * expressions for exp, you should use constructions such as
		 *
		 * <code>if (__builtin_expect (ptr != NULL, 1)) foo (*ptr);</code>
		 *
		 * when testing pointer or floating-point values.
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		final ExpressionResult arg1 = dispatchAndConvert(main, loc, arguments[0]);
		final ExpressionResult arg2 = dispatchAndConvert(main, loc, arguments[1]);
		return combineExpressionResults(arg1.getLrValue(), arg1, arg2);
	}

	private static ExpressionResult handleAbort(final ILocation loc) {
		return new ExpressionResult(Collections.singletonList(new AssumeStatement(loc, new BooleanLiteral(loc, false))),
				null);
	}

	private Result handleVerifierNonDet(final Dispatcher main, final ILocation loc, final CType cType) {
		final List<Statement> stmt = new ArrayList<>();
		final List<Declaration> decl = new ArrayList<>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final ASTType type = mTypeHandler.cType2AstType(loc, cType);
		final String tmpName = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, cType);
		final VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpName, type, loc);
		decl.add(tVarDecl);
		auxVars.put(tVarDecl, loc);

		final LRValue returnValue = new RValue(new IdentifierExpression(loc, tmpName), cType);
		mExpressionTranslation.addAssumeValueInRangeStatements(loc, returnValue.getValue(), returnValue.getCType(),
				stmt);

		assert CHandler.isAuxVarMapComplete(main.mNameHandler, decl, auxVars);
		return new ExpressionResult(stmt, returnValue, decl, auxVars);
	}

	private Result handleVerifierAssume(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		// according to SV-Comp specification assume takes only one argument, but the code allows more than one
		checkArguments(loc, 1, name, node.getArguments());

		final List<Expression> args = new ArrayList<>();
		final List<ExpressionResult> results = new ArrayList<>();
		for (final IASTInitializerClause inParam : node.getArguments()) {
			final ExpressionResult in = dispatchAndConvert(main, loc, inParam);
			if (in.mLrVal.getValue() == null) {
				final String msg = "Incorrect or invalid in-parameter! " + loc.toString();
				throw new IncorrectSyntaxException(loc, msg);
			}
			in.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);
			args.add(in.getLrValue().getValue());
			results.add(in);
		}

		final ExpressionResult rtr = combineExpressionResults(null, results);
		for (final Expression a : args) {
			// could just take the first as there is only one, but it's so easy to make it more general..
			rtr.addStatement(new AssumeStatement(loc, a));
		}
		assert CHandler.isAuxVarMapComplete(main.mNameHandler, rtr.getDeclarations(), rtr.getAuxVars());
		return rtr;
	}

	private Result handleNaNOrInfinity(final ILocation loc, final String methodName) {
		return mExpressionTranslation.createNanOrInfinity(loc, methodName);
	}

	private Result handleUnaryFloatFunction(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final FloatFunction floatFunction = FloatFunction.decode(name);
		final ExpressionResult arg = handleFloatArguments(main, node, loc, name, 1, floatFunction).get(0);
		final RValue rvalue =
				mExpressionTranslation.constructOtherUnaryFloatOperation(loc, floatFunction, (RValue) arg.mLrVal);
		return combineExpressionResults(rvalue, arg);
	}

	private Result handleBinaryFloatFunction(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final FloatFunction floatFunction = FloatFunction.decode(name);
		final List<ExpressionResult> args = handleFloatArguments(main, node, loc, name, 2, floatFunction);
		final RValue rvalue = mExpressionTranslation.constructOtherBinaryFloatOperation(loc, floatFunction,
				(RValue) args.get(0).getLrValue(), (RValue) args.get(1).getLrValue());
		return combineExpressionResults(rvalue, args);
	}

	private List<ExpressionResult> handleFloatArguments(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final int numberOfArgs, final FloatFunction floatFunction) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, numberOfArgs, name, arguments);
		if (floatFunction == null) {
			throw new IllegalArgumentException(
					"Ultimate declared float handling for " + name + ", but is not known float function");
		}
		final List<ExpressionResult> rtr = new ArrayList<>();
		for (final IASTInitializerClause argument : arguments) {
			final ExpressionResult arg = dispatchAndConvert(main, loc, argument);
			mExpressionTranslation.convertIfNecessary(loc, arg, floatFunction.getType());
			rtr.add(arg);
		}

		final CPrimitive typeDeterminedByName = floatFunction.getType();
		if (typeDeterminedByName != null) {
			for (final ExpressionResult arg : rtr) {
				mExpressionTranslation.convertFloatToFloat(loc, arg, typeDeterminedByName);
			}

		}
		return rtr;
	}

	private Result handleFloatBuiltinBinaryComparison(final Dispatcher main, final IASTFunctionCallExpression node,
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

		final ExpressionResult rl = dispatchAndConvert(main, loc, arguments[0]);
		final ExpressionResult rr = dispatchAndConvert(main, loc, arguments[1]);

		// Note: this works because SMTLIB already ensures that all comparisons return false if one of the arguments is
		// NaN

		return mCHandler.handleRelationalOperators(main, loc, op, rl, rr);
	}

	private Result handleFloatBuiltinIsUnordered(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		/*
		 * http://en.cppreference.com/w/c/numeric/math/isunordered
		 *
		 * int isunordered (real-floating x, real-floating y)
		 *
		 * This macro determines whether its arguments are unordered. In other words, it is true if x or y are NaN, and
		 * false otherwise.
		 *
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);

		final ExpressionResult leftRvaluedResult = dispatchAndConvert(main, loc, arguments[0]);
		final ExpressionResult rightRvaluedResult = dispatchAndConvert(main, loc, arguments[1]);
		final ExpressionResult nanLResult = mExpressionTranslation.createNanOrInfinity(loc, "NAN");
		final ExpressionResult nanRResult = mExpressionTranslation.createNanOrInfinity(loc, "NAN");

		mExpressionTranslation.usualArithmeticConversions(loc, nanLResult, leftRvaluedResult);
		final BinaryExpression leftExpr = new BinaryExpression(loc, Operator.COMPEQ,
				leftRvaluedResult.getLrValue().getValue(), nanLResult.getLrValue().getValue());

		mExpressionTranslation.usualArithmeticConversions(loc, nanRResult, rightRvaluedResult);
		final BinaryExpression rightExpr = new BinaryExpression(loc, Operator.COMPEQ,
				rightRvaluedResult.getLrValue().getValue(), nanRResult.getLrValue().getValue());
		final BinaryExpression expr = new BinaryExpression(loc, Operator.LOGICOR, leftExpr, rightExpr);
		final LRValue lrVal = new RValue(expr, new CPrimitive(CPrimitives.INT), true);
		final ExpressionResult rtr =
				combineExpressionResults(lrVal, leftRvaluedResult, rightRvaluedResult, nanLResult, nanRResult);
		assert CHandler.isAuxVarMapComplete(main.mNameHandler, rtr.getDeclarations(), rtr.getAuxVars());
		return rtr;
	}

	private Result handleFloatBuiltinIsLessGreater(final Dispatcher main, final IASTFunctionCallExpression node,
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

		final ExpressionResult leftRvaluedResult = dispatchAndConvert(main, loc, arguments[0]);
		final ExpressionResult rightRvaluedResult = dispatchAndConvert(main, loc, arguments[1]);
		mExpressionTranslation.usualArithmeticConversions(loc, leftRvaluedResult, rightRvaluedResult);

		final ExpressionResult lessThan = mCHandler.handleRelationalOperators(main, loc,
				IASTBinaryExpression.op_lessThan, leftRvaluedResult, rightRvaluedResult);
		final ExpressionResult greaterThan = mCHandler.handleRelationalOperators(main, loc,
				IASTBinaryExpression.op_greaterThan, leftRvaluedResult, rightRvaluedResult);

		final BinaryExpression expr = new BinaryExpression(loc, Operator.LOGICOR, lessThan.getLrValue().getValue(),
				greaterThan.getLrValue().getValue());
		final LRValue lrVal = new RValue(expr, new CPrimitive(CPrimitives.INT), true);
		final ExpressionResult rtr = combineExpressionResults(lrVal, lessThan, greaterThan);
		assert CHandler.isAuxVarMapComplete(main.mNameHandler, rtr.getDeclarations(), rtr.getAuxVars());
		return rtr;
	}

	private Result handleBuiltinObjectSize(final Dispatcher main, final ILocation loc) {
		main.warn(loc, "used trivial implementation of __builtin_object_size");
		final CPrimitive cType = new CPrimitive(CPrimitives.INT);
		final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(loc, cType, BigInteger.ZERO);
		return new ExpressionResult(new RValue(zero, cType));
	}

	private Result handlePrintF(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc) {
		// skip if parent of parent is CompoundStatement
		// otherwise, replace by havoced variable
		if (node.getParent().getParent() instanceof IASTCompoundStatement) {
			return new SkipResult();
		}

		final List<Statement> stmt = new ArrayList<>();
		final List<Declaration> decl = new ArrayList<>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final List<Overapprox> overappr = new ArrayList<>();

		// 2015-11-05 Matthias: TODO check if int is reasonable here
		final ASTType tempType = mTypeHandler.cType2AstType(loc, new CPrimitive(CPrimitives.INT));
		final String tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, null);
		final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0],
				new VarList[] { new VarList(loc, new String[] { tId }, tempType) });
		auxVars.put(tVarDecl, loc);
		decl.add(tVarDecl);
		stmt.add(new HavocStatement(loc, new VariableLHS[] { new VariableLHS(loc, tId) }));
		final LRValue returnValue = new RValue(new IdentifierExpression(loc, tId), null);
		assert CHandler.isAuxVarMapComplete(main.mNameHandler, decl, auxVars);
		return new ExpressionResult(stmt, returnValue, decl, auxVars, overappr);
	}

	private Result handleMemCopy(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 3, name, arguments);
		final ExpressionResult dest = dispatchAndConvert(main, loc, arguments[0]);
		main.mCHandler.convert(loc, dest, new CPointer(new CPrimitive(CPrimitives.VOID)));
		final ExpressionResult src = dispatchAndConvert(main, loc, arguments[1]);
		main.mCHandler.convert(loc, src, new CPointer(new CPrimitive(CPrimitives.VOID)));
		final ExpressionResult size = dispatchAndConvert(main, loc, arguments[2]);
		main.mCHandler.convert(loc, size, mTypeSizeComputer.getSizeT());

		final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(dest, src, size);

		final String tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.MEMCPYRES, dest.mLrVal.getCType());
		final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0],
				new VarList[] { new VarList(loc, new String[] { tId }, main.mTypeHandler.constructPointerType(loc)) });
		result.mDecl.add(tVarDecl);
		result.mAuxVars.put(tVarDecl, loc);

		final Statement call = mMemoryHandler.constructMemcpyCall(loc, dest.mLrVal.getValue(), src.mLrVal.getValue(),
				size.mLrVal.getValue(), tId);
		result.mStmt.add(call);
		result.mLrVal = new RValue(new IdentifierExpression(loc, tId), new CPointer(new CPrimitive(CPrimitives.VOID)));

		// add required information to function handler.
		mFunctionHandler.addCallGraphNode(MemoryModelDeclarations.C_Memcpy.getName());
		mFunctionHandler.addCallGraphEdge(mFunctionHandler.getCurrentProcedureID(),
				MemoryModelDeclarations.C_Memcpy.getName());
		mFunctionHandler.addModifiedGlobalEntry(MemoryModelDeclarations.C_Memcpy.getName());

		return result;
	}

	private static Result handleErrorFunction(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc) {
		final boolean checkSvcompErrorfunction =
				main.getPreferences().getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_SVCOMP_ERRORFUNCTION);
		final Expression falseLiteral = new BooleanLiteral(loc, new InferredType(Type.Boolean), false);
		Statement st;
		if (checkSvcompErrorfunction) {
			final Check check = new Check(Spec.ERROR_FUNCTION);
			st = new AssertStatement(loc, falseLiteral);
			check.annotate(st);
		} else {
			st = new AssumeStatement(loc, falseLiteral);
		}
		return new ExpressionResult(Collections.singletonList(st), null);
	}

	private static Result handleLtlStep(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc) {
		final LTLStepAnnotation ltlStep = new LTLStepAnnotation();
		final AssumeStatement assumeStmt =
				new AssumeStatement(loc, new BooleanLiteral(loc, new InferredType(Type.Boolean), true));
		ltlStep.annotate(assumeStmt);
		return new ExpressionResult(Collections.singletonList(assumeStmt), null);
	}

	private static Result handleByIgnore(final Dispatcher main, final ILocation loc, final String methodName) {
		main.warn(loc, "ignored call to " + methodName);
		return new SkipResult();
	}

	private static Result handleByUnsupportedSyntaxException(final ILocation loc, final String functionName) {
		throw new UnsupportedSyntaxException(loc, "Unsupported function: " + functionName);
	}

	private static Result handleByUnsupportedSyntaxExceptionKnown(final ILocation loc, final String lib,
			final String functionName) {
		throw new UnsupportedSyntaxException(loc, "Unsupported function from " + lib + ": " + functionName);
	}

	private static Result handleByOverapproximation(final Dispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String methodName, final int numberOfArgs, final CType resultType) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, numberOfArgs, methodName, arguments);
		final List<ExpressionResult> results = new ArrayList<>();
		for (final IASTInitializerClause argument : arguments) {
			results.add((ExpressionResult) main.dispatch(argument));
		}

		final ExpressionResult overapproxCall =
				constructOverapproximationForFunctionCall(main, loc, methodName, resultType);
		results.add(overapproxCall);
		return combineExpressionResults(overapproxCall.getLrValue(), results);
	}

	private static ExpressionResult combineExpressionResults(final LRValue finalLRValue,
			final List<ExpressionResult> results) {
		final List<Statement> stmt = new ArrayList<>();
		final List<Declaration> decl = new ArrayList<>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final List<Overapprox> overapprox = new ArrayList<>();
		final List<ExpressionResult> unionFields = new ArrayList<>();
		for (final ExpressionResult result : results) {
			stmt.addAll(result.getStatements());
			decl.addAll(result.getDeclarations());
			auxVars.putAll(result.getAuxVars());
			overapprox.addAll(result.getOverapprs());
			unionFields.addAll(result.getNeighbourUnionFields());
		}

		return new ExpressionResult(stmt, finalLRValue, decl, auxVars, overapprox, unionFields);
	}

	private static ExpressionResult combineExpressionResults(final LRValue finalLRValue,
			final ExpressionResult... results) {
		return combineExpressionResults(finalLRValue, Arrays.stream(results).collect(Collectors.toList()));
	}

	/**
	 * Creates a function call expression for the ~free(e) function!
	 *
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param fh
	 *            a reference to the FunctionHandler - required to add informations to the call graph.
	 * @param e
	 *            the expression referring to the pointer, that should be free'd.
	 * @param loc
	 *            Location for errors and new nodes in the AST.
	 * @return a function call expression for ~free(e).
	 */
	private CallStatement getFreeCall(final Dispatcher main, final LRValue lrVal, final ILocation loc) {
		assert lrVal instanceof RValue || lrVal instanceof LocalLValue;
		mMemoryHandler.getRequiredMemoryModelFeatures().require(MemoryModelDeclarations.Free);

		// Further checks are done in the precondition of ~free()!
		// ~free(E);
		final CallStatement freeCall =
				new CallStatement(loc, false, new VariableLHS[0], SFO.FREE, new Expression[] { lrVal.getValue() });
		// add required information to function handler.
		if (mFunctionHandler.getCurrentProcedureID() != null) {
			mFunctionHandler.addModifiedGlobal(SFO.FREE, SFO.VALID);
			mFunctionHandler.addCallGraphNode(SFO.FREE);
			mFunctionHandler.addCallGraphEdge(mFunctionHandler.getCurrentProcedureID(), SFO.FREE);
		}
		return freeCall;
	}

	/**
	 * Construct assert statements that do memsafety checks for {@link pointerValue} if the corresponding settings are
	 * active. settings concerned are: - "Pointer base address is valid at dereference" - "Pointer to allocated memory
	 * at dereference"
	 */
	private static List<Statement> constructMemsafetyChecksForPointerExpression(final ILocation loc,
			final Expression pointerValue, final MemoryHandler memoryHandler,
			final ExpressionTranslation expressionTranslation) {
		final List<Statement> result = new ArrayList<>();

		if (memoryHandler.getPointerBaseValidityCheckMode() != PointerCheckMode.IGNORE) {

			// valid[s.base]
			final Expression validBase = memoryHandler.constructPointerBaseValidityCheck(loc, pointerValue);

			if (memoryHandler.getPointerBaseValidityCheckMode() == PointerCheckMode.ASSERTandASSUME) {
				final AssertStatement assertion = new AssertStatement(loc, validBase);
				final Check chk = new Check(Spec.MEMORY_DEREFERENCE);
				chk.annotate(assertion);
				result.add(assertion);
			} else {
				assert memoryHandler.getPointerBaseValidityCheckMode() == PointerCheckMode.ASSUME : "missed a case?";
				final Statement assume = new AssumeStatement(loc, validBase);
				result.add(assume);
			}
		}
		if (memoryHandler.getPointerTargetFullyAllocatedCheckMode() != PointerCheckMode.IGNORE) {

			// s.offset < length[s.base])
			final Expression offsetSmallerLength = expressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_lessThan, MemoryHandler.getPointerOffset(pointerValue, loc),
					expressionTranslation.getCTypeOfPointerComponents(),
					ExpressionFactory.constructNestedArrayAccessExpression(loc, memoryHandler.getLengthArray(loc),
							new Expression[] { MemoryHandler.getPointerBaseAddress(pointerValue, loc) }),
					expressionTranslation.getCTypeOfPointerComponents());

			// s.offset >= 0;
			final Expression offsetNonnegative = expressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_greaterEqual, MemoryHandler.getPointerOffset(pointerValue, loc),
					expressionTranslation.getCTypeOfPointerComponents(),
					expressionTranslation.constructLiteralForIntegerType(loc,
							expressionTranslation.getCTypeOfPointerComponents(), new BigInteger("0")),
					expressionTranslation.getCTypeOfPointerComponents());

			final Expression aAndB =
					new BinaryExpression(loc, Operator.LOGICAND, offsetSmallerLength, offsetNonnegative);
			if (memoryHandler.getPointerBaseValidityCheckMode() == PointerCheckMode.ASSERTandASSUME) {
				final AssertStatement assertion = new AssertStatement(loc, aAndB);
				final Check chk = new Check(Spec.MEMORY_DEREFERENCE);
				chk.annotate(assertion);
				result.add(assertion);
			} else {
				assert memoryHandler.getPointerBaseValidityCheckMode() == PointerCheckMode.ASSUME : "missed a case?";
				final Statement assume = new AssumeStatement(loc, aAndB);
				result.add(assume);
			}
		}
		return result;
	}

	private static void checkArguments(final ILocation loc, final int expectedArgs, final String name,
			final IASTInitializerClause[] arguments) {
		if (arguments.length != expectedArgs) {
			throw new IncorrectSyntaxException(loc,
					name + " has only " + expectedArgs + " arguments, but was called with " + arguments.length);
		}
	}

	private static ExpressionResult dispatchAndConvert(final Dispatcher main, final ILocation loc,
			final IASTInitializerClause initClause) {
		return ((ExpressionResult) main.dispatch(initClause)).switchToRValueIfNecessary(main, loc);
	}

	private static <K, V> void fill(final Map<K, V> map, final K key, final V value) {
		final V old = map.put(key, value);
		if (old != null) {
			throw new AssertionError("Accidentally overwrote definition for " + key);
		}
	}

	private static ILocation getLoc(final Dispatcher main, final IASTFunctionCallExpression node) {
		final ILocation loc;
		if (main.isSvcomp()) {
			loc = main.getLocationFactory().createCLocation(node, new Check(Check.Spec.PRE_CONDITION));
		} else {
			loc = main.getLocationFactory().createCLocation(node);
		}
		return loc;
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	@FunctionalInterface
	private interface IFunctionModelHandler {
		Result handleFunction(final Dispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
				String methodName);
	}
}
