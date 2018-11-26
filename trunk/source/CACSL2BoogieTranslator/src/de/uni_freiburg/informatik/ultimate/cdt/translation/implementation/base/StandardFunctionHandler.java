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
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTIdExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.LocalLValueILocationPair;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.FloatFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.FloatSupportInUltimate;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
//import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
//import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValueFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LTLStepAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * The {@link StandardFunctionHandler} creates the translation for various functions where we have our own specification
 * or implementation. This is typically the case for functions defined in the C standard, but also for various standard
 * libraries or SV-COMP extensions.
 *
 * @author Markus Lindenmann,
 * @author Matthias Heizmann
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class StandardFunctionHandler {

	private final LocationFactory mLocationFactory;

	private final Map<String, IFunctionModelHandler> mFunctionModels;

	private final ExpressionTranslation mExpressionTranslation;

	private final MemoryHandler mMemoryHandler;

	private final TypeSizeAndOffsetComputer mTypeSizeComputer;

	private final ProcedureManager mProcedureManager;

	private final CHandler mCHandler;

	private final CTranslationResultReporter mReporter;

	private final Map<String, IASTNode> mFunctionTable;

	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	private final INameHandler mNameHandler;

	private final TypeSizes mTypeSizes;

	private final FlatSymbolTable mSymboltable;

	private final TranslationSettings mSettings;

	private final ExpressionResultTransformer mExprResultTransformer;

	private final ITypeHandler mTypeHandler;

	private int mPthreadCreateCounter = 0;

	public StandardFunctionHandler(final Map<String, IASTNode> functionTable, final AuxVarInfoBuilder auxVarInfoBuilder,
			final INameHandler nameHandler, final ExpressionTranslation expressionTranslation,
			final MemoryHandler memoryHandler, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final ProcedureManager procedureManager, final CHandler cHandler, final CTranslationResultReporter reporter,
			final TypeSizes typeSizes, final FlatSymbolTable symboltable, final TranslationSettings settings,
			final ExpressionResultTransformer expressionResultTransformer, final LocationFactory locationFactory,
			final ITypeHandler typeHandler) {
		mExpressionTranslation = expressionTranslation;
		mMemoryHandler = memoryHandler;
		mTypeSizeComputer = typeSizeAndOffsetComputer;
		mProcedureManager = procedureManager;
		mCHandler = cHandler;
		mReporter = reporter;
		mFunctionTable = functionTable;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mNameHandler = nameHandler;
		mTypeSizes = typeSizes;
		mSymboltable = symboltable;
		mSettings = settings;
		mExprResultTransformer = expressionResultTransformer;
		mLocationFactory = locationFactory;
		mTypeHandler = typeHandler;

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
	public Result translateStandardFunction(final IDispatcher main, final IASTFunctionCallExpression node,
			final IASTIdExpression astIdExpression) {
		assert node
				.getFunctionNameExpression() == astIdExpression : "astIdExpression is not the name of the called function";
		final String name = astIdExpression.getName().toString();
		final IFunctionModelHandler functionModel = mFunctionModels.get(name);
		if (functionModel != null) {
			final String transformedName = mSymboltable.applyMultiparseRenaming(node.getContainingFilename(), name);
			final IASTNode funDecl = mFunctionTable.get(transformedName);
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

		/** functions of pthread library **/
		fill(map, "pthread_create", this::handlePthread_create);
		fill(map, "pthread_join", this::handlePthread_join);
		fill(map, "pthread_mutex_init", this::handlePthread_mutex_init);
		fill(map, "pthread_mutex_lock", this::handlePthread_mutex_lock);
		fill(map, "pthread_mutex_unlock", this::handlePthread_mutex_unlock);
		fill(map, "pthread_exit", this::handlePthread_exit);
		fill(map, "pthread_cond_init", die);
		fill(map, "pthread_cond_wait", die);
		fill(map, "pthread_cond_signal", die);
		fill(map, "pthread_cond_destroy", die);
		fill(map, "pthread_cond_broadcast", die);
		fill(map, "pthread_mutex_destroy", skip);
		// the following three occur at SV-COMP 2019 only in one benchmark
		fill(map, "pthread_attr_init", die);
		fill(map, "pthread_attr_setdetachstate", die);
		fill(map, "pthread_attr_destroy", die);
		// the following three occur at SV-COMP 2019 only in some pthread-divine benchmarks
		fill(map, "pthread_key_create", die);
		fill(map, "pthread_getspecific", die);
		fill(map, "pthread_setspecific", die);

		fill(map, "printf", (main, node, loc, name) -> handlePrintF(main, node, loc));

		fill(map, "__builtin_memcpy", this::handleMemcpy);
		fill(map, "__memcpy", this::handleMemcpy);
		fill(map, "memcpy", this::handleMemcpy);

		fill(map, "__builtin_memmove", this::handleMemmove);
		fill(map, "__memmove", this::handleMemmove);
		fill(map, "memmove", this::handleMemmove);

		fill(map, "alloca", this::handleAlloc);
		fill(map, "__builtin_alloca", this::handleAlloc);
		fill(map, "memset", this::handleMemset);

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
		 * Current solution: replace call by a havoced aux variable.
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
		fill(map, "__builtin_object_size", this::handleBuiltinObjectSize);

		/** various string builtins **/
		fill(map, "__builtin_strchr", this::handleStrChr);
		fill(map, "strchr", this::handleStrChr);
		fill(map, "__builtin_strlen", this::handleStrLen);
		fill(map, "strlen", this::handleStrLen);
		fill(map, "__builtin_strcmp", this::handleStrCmp);
		fill(map, "strcmp", this::handleStrCmp);
		fill(map, "strcpy", this::handleStrCpy);

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

		// see 7.12.9.8 or http://en.cppreference.com/w/c/numeric/math/trunc
		fill(map, "trunc", this::handleUnaryFloatFunction);
		fill(map, "truncf", this::handleUnaryFloatFunction);
		fill(map, "truncl", this::handleUnaryFloatFunction);

		// see 7.12.9.6 or http://en.cppreference.com/w/c/numeric/math/round
		fill(map, "round", this::handleUnaryFloatFunction);
		fill(map, "roundf", this::handleUnaryFloatFunction);
		fill(map, "roundl", this::handleUnaryFloatFunction);
		// see 7.12.9.7 or http://en.cppreference.com/w/c/numeric/math/round
		fill(map, "lround", this::handleUnaryFloatFunction);
		fill(map, "lroundf", this::handleUnaryFloatFunction);
		fill(map, "lroundl", this::handleUnaryFloatFunction);
		fill(map, "llround", this::handleUnaryFloatFunction);
		fill(map, "llroundf", this::handleUnaryFloatFunction);
		fill(map, "llroundl", this::handleUnaryFloatFunction);

		// see 7.12.9.2 or http://en.cppreference.com/w/c/numeric/math/floor
		fill(map, "floor", this::handleUnaryFloatFunction);
		fill(map, "floorf", this::handleUnaryFloatFunction);
		fill(map, "floorl", this::handleUnaryFloatFunction);

		// see 7.12.9.1 or http://en.cppreference.com/w/c/numeric/math/ceil
		fill(map, "ceil", this::handleUnaryFloatFunction);
		fill(map, "ceilf", this::handleUnaryFloatFunction);
		fill(map, "ceill", this::handleUnaryFloatFunction);

		// see 7.12.4.6 or http://en.cppreference.com/w/c/numeric/math/sin
		fill(map, "sin", this::handleUnaryFloatFunction);
		fill(map, "sinf", this::handleUnaryFloatFunction);
		fill(map, "sinl", this::handleUnaryFloatFunction);

		// see 7.12.12.2 or http://en.cppreference.com/w/c/numeric/math/fmax
		// NaN arguments are treated as missing data: if one argument is a NaN and the
		// other numeric, then the
		// fmin/fmax functions choose the numeric value.
		fill(map, "fmax", this::handleBinaryFloatFunction);
		fill(map, "fmaxf", this::handleBinaryFloatFunction);
		fill(map, "fmaxl", this::handleBinaryFloatFunction);

		// see 7.12.12.3 or http://en.cppreference.com/w/c/numeric/math/fmin
		fill(map, "fmin", this::handleBinaryFloatFunction);
		fill(map, "fminf", this::handleBinaryFloatFunction);
		fill(map, "fminl", this::handleBinaryFloatFunction);

		// see 7.12.10.2 or http://en.cppreference.com/w/c/numeric/math/remainder
		fill(map, "remainder", this::handleBinaryFloatFunction);
		fill(map, "remainderf", this::handleBinaryFloatFunction);
		fill(map, "remainderl", this::handleBinaryFloatFunction);

		// see 7.12.10.1 or http://en.cppreference.com/w/c/numeric/math/fmod
		fill(map, "fmod", this::handleBinaryFloatFunction);
		fill(map, "fmodf", this::handleBinaryFloatFunction);
		fill(map, "fmodl", this::handleBinaryFloatFunction);

		// see 7.12.11.1 or http://en.cppreference.com/w/c/numeric/math/copysign
		fill(map, "copysign", this::handleBinaryFloatFunction);
		fill(map, "copysignf", this::handleBinaryFloatFunction);
		fill(map, "copysignl", this::handleBinaryFloatFunction);

		// see 7.12.12.1 or https://en.cppreference.com/w/c/numeric/math/fdim
		fill(map, "fdim", this::handleBinaryFloatFunction);
		fill(map, "fdimf", this::handleBinaryFloatFunction);
		fill(map, "fdiml", this::handleBinaryFloatFunction);

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

		// from fenv.h
		fill(map, "fegetround", this::handleBuiltinFegetround);
		fill(map, "fesetround", this::handleBuiltinFesetround);

		/** Begin <stdlib.h> functions according to 7.22 General utilities <stdlib.h> **/
		/**
		 * 7.22.1 Numeric conversion functions
		 *
		 * 7.22.1.1 The atof function
		 *
		 * 7.22.1.2 The atoi, atol, and atoll functions
		 *
		 * The functions atof, atoi, atol, and atoll ... If the value of the result cannot be represented, the behavior
		 * is undefined.
		 *
		 * see https://en.cppreference.com/w/c/string/byte/atof
		 *
		 * double value corresponding to the contents of str on success. If the converted value falls out of range of
		 * the return type, the return value is undefined. If no conversion can be performed, 0.0 is returned.
		 *
		 * see https://en.cppreference.com/w/c/string/byte/atoi
		 *
		 * Integer value corresponding to the contents of str on success. If the converted value falls out of range of
		 * corresponding return type, the return value is undefined. If no conversion can be performed, ​0​ is returned.
		 *
		 * We handle this by overapproximation and do not check for undefined behavior.
		 */
		fill(map, "atof", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.DOUBLE)));
		fill(map, "atoi", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.INT)));
		fill(map, "atol", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.LONG)));
		fill(map, "atoll", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 1,
				new CPrimitive(CPrimitives.LONGLONG)));

		/**
		 * 7.22.1.3 The strtod, strtof, and strtold functions
		 *
		 * see https://en.cppreference.com/w/c/string/byte/strtof
		 *
		 * Interprets a floating-point value in a byte string pointed to by str. 2 arguments: pointer to the
		 * null-terminated byte string to be interpreted and pointer to a pointer to character.
		 *
		 * Floating-point value corresponding to the contents of str on success. If the converted value falls out of
		 * range of corresponding return type, range error occurs and HUGE_VAL, HUGE_VALF or HUGE_VALL is returned. If
		 * no conversion can be performed, ​0​ is returned.
		 *
		 * We handle this by overapproximation and do not check of range errors.
		 *
		 */
		fill(map, "strtof", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 2,
				new CPrimitive(CPrimitives.FLOAT)));
		fill(map, "strtod", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 2,
				new CPrimitive(CPrimitives.DOUBLE)));
		fill(map, "strtold", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name, 2,
				new CPrimitive(CPrimitives.LONGDOUBLE)));

		/**
		 * 7.22.2.1 The rand function
		 *
		 * see https://en.cppreference.com/w/c/numeric/random/rand
		 *
		 * Pseudo-random integer value between ​0​ and RAND_MAX, inclusive. The value of the RAND_MAX macro shall be at
		 * least 32767.
		 *
		 * We handle this similar to handleVerifierNonDet, but we limit the return type to positive range of int.
		 *
		 * We ignore seeding with srand.
		 */
		fill(map, "rand", this::handleRand);

		/**
		 * 7.22.2.2 The srand function
		 *
		 * see https://en.cppreference.com/w/c/numeric/random/srand
		 *
		 * The srand function uses the argument as a seed for a new sequence of pseudo-random numbers to be returned by
		 * subsequent calls to rand.
		 *
		 * We can safely skip this function.
		 */
		fill(map, "srand", (main, node, loc, name) -> handleVoidFunctionBySkipAndDispatch(main, node, loc, name, 1));

		/**
		 * 7.22.3 Memory management functions
		 *
		 * 7.22.3.1 The aligned_alloc function, 7.22.3.2 The calloc function, 7.22.3.3 The free function, 7.22.3.4 The
		 * malloc function, 7.22.3.5 The realloc function
		 */
		fill(map, "aligned_alloc", die);
		fill(map, "calloc", this::handleCalloc);
		fill(map, "free", this::handleFree);
		fill(map, "malloc", this::handleAlloc);
		fill(map, "realloc", die);

		/**
		 * @formatter:off
		 * 7.22.4 Communication with the environment
		 *
		 * 7.22.4.1 The abort function
		 * 7.22.4.2 The atexit function
		 * 7.22.4.3 The at_quick_exit function
		 * 7.22.4.4 The exit function
		 * 7.22.4.5 The _Exit function
		 * 7.22.4.6 The getenv function
		 * 7.22.4.7 The quick_exit function
		 * 7.22.4.8 The system function
		 * @formatter:on
		 */
		fill(map, "abort", (main, node, loc, name) -> handleAbort(loc));
		fill(map, "atexit", die);
		fill(map, "at_quick_exit", die);
		// TODO: Find out what SVCOMP expects from exit()
		// fill(map, "exit", die);
		fill(map, "_Exit", die);
		fill(map, "getenv", die);
		fill(map, "quick_exit", die);
		fill(map, "system", die);

		/**
		 * @formatter:off
		 * 7.22.5 Searching and sorting utilities
		 *
		 * 7.22.5.1 The bsearch function
		 * 7.22.5.2 The qsort function
		 * @formatter:on
		 */
		fill(map, "bsearch", die);
		fill(map, "qsort", die);

		/**
		 * @formatter:off
		 * 7.22.6 Integer arithmetic functions
		 *
		 * 7.22.6.1 The abs, labs and llabs functions
		 * 7.22.6.2 The div, ldiv, and lldiv functions
		 * @formatter:on
		 */
		fill(map, "abs", die);
		fill(map, "labs", die);
		fill(map, "llabs", die);
		fill(map, "div", die);
		fill(map, "ldiv", die);
		fill(map, "lldiv", die);

		/**
		 * @formatter:off
		 * 7.22.7 Multibyte/wide character conversion functions
		 *
		 * 7.22.7.1 The mblen function
		 * 7.22.7.2 The mbtowc function
		 * 7.22.7.3 The wctomb function
		 *
		 * @formatter:on
		 */
		fill(map, "mblen", die);
		fill(map, "mbtowc", die);
		fill(map, "wctomb", die);

		/**
		 * @formatter:off
		 * 7.22.8 Multibyte/wide string conversion functions
		 *
		 * 7.22.8.1 The mbstowcs function
		 * 7.22.8.2 The wcstombs function
		 * @formatter:on
		 */
		fill(map, "mbstowcs", die);
		fill(map, "wcstombs", die);

		/** End <stdlib.h> functions according to 7.22 General utilities <stdlib.h> **/

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

	private Result handleStrCmp(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult arg0 =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);
		builder.addDeclarations(arg0.getDeclarations());
		builder.addStatements(arg0.getStatements());
		builder.addOverapprox(arg0.getOverapprs());
		builder.addAuxVars(arg0.getAuxVars());
		builder.addNeighbourUnionFields(arg0.getNeighbourUnionFields());

		builder.addStatements(
				mMemoryHandler.constructMemsafetyChecksForPointerExpression(loc, arg0.getLrValue().getValue()));

		final ExpressionResult arg1 =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[1]);
		builder.addDeclarations(arg1.getDeclarations());
		builder.addStatements(arg1.getStatements());
		builder.addOverapprox(arg1.getOverapprs());
		builder.addAuxVars(arg1.getAuxVars());
		builder.addNeighbourUnionFields(arg1.getNeighbourUnionFields());

		builder.addStatements(
				mMemoryHandler.constructMemsafetyChecksForPointerExpression(loc, arg1.getLrValue().getValue()));

		final CPrimitive resultType = new CPrimitive(CPrimitives.INT);
		// introduce fresh aux variable
		// final String tmpId = mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, resultType);
		// final VariableDeclaration tmpVarDecl =
		// SFO.getTempVarVariableDeclaration(tmpId, main.mTypeHandler.cType2AstType(loc, resultType), loc);
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.NONDET);
		builder.addDeclaration(auxvarinfo.getVarDec());
		builder.addAuxVar(auxvarinfo);

		final Overapprox overAppFlag = new Overapprox(name, loc);
		builder.addOverapprox(overAppFlag);
		final RValue lrVal = new RValue(auxvarinfo.getExp(), resultType);
		builder.setLrValue(lrVal);
		return builder.build();
	}

	/**
	 *
	 * char *strcpy( char *dest, const char *src );
	 *
	 * @param main
	 * @param node
	 * @param loc
	 * @param name
	 * @return
	 */
	private Result handleStrCpy(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {

		final MemoryModelDeclarations strCpyMmDecl = MemoryModelDeclarations.C_StrCpy;

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		final CPointer charPointerType = new CPointer(new CPrimitive(CPrimitives.CHAR));
		final ExpressionResult dest = mExprResultTransformer.dispatchDecaySwitchToRValueConvertFunctionArgument(main,
				loc, arguments[0], charPointerType);
		final ExpressionResult src = mExprResultTransformer.dispatchDecaySwitchToRValueConvertFunctionArgument(main,
				loc, arguments[1], charPointerType);

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		resultBuilder.addAllExceptLrValue(dest);
		resultBuilder.addAllExceptLrValue(src);

		final AuxVarInfo auxvarinfo =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, dest.getLrValue().getCType(), SFO.AUXVAR.STRCPYRES);

		final CallStatement call = StatementFactory.constructCallStatement(loc, false,
				new VariableLHS[] { auxvarinfo.getLhs() }, strCpyMmDecl.getName(),
				new Expression[] { dest.getLrValue().getValue(), src.getLrValue().getValue() });
		resultBuilder.addDeclaration(auxvarinfo.getVarDec());
		resultBuilder.addAuxVar(auxvarinfo);
		resultBuilder.addStatement(call);
		resultBuilder.setLrValue(new RValue(auxvarinfo.getExp(), new CPointer(new CPrimitive(CPrimitives.VOID))));

		// add marker for global declaration to memory handler
		mMemoryHandler.requireMemoryModelFeature(strCpyMmDecl);

		// add required information to function handler.
		mProcedureManager.registerProcedure(strCpyMmDecl.getName());
		// mProcedureManager.registerCall(mmDecl.getName());

		return resultBuilder.build();
	}

	private Result handleStrLen(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String methodName) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, methodName, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();

		final ExpressionResult arg =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);
		builder.addDeclarations(arg.getDeclarations());
		builder.addStatements(arg.getStatements());
		builder.addOverapprox(arg.getOverapprs());
		builder.addAuxVars(arg.getAuxVars());
		builder.addNeighbourUnionFields(arg.getNeighbourUnionFields());

		builder.addStatements(
				mMemoryHandler.constructMemsafetyChecksForPointerExpression(loc, arg.getLrValue().getValue()));

		// according to standard result is size_t, we use int for efficiency
		final CPrimitive resultType = new CPrimitive(CPrimitives.INT);
		// introduce fresh aux variable
		// final String tmpId = mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, resultType);
		// final VariableDeclaration tmpVarDecl =
		// SFO.getTempVarVariableDeclaration(tmpId, main.mTypeHandler.cType2AstType(loc, resultType), loc);
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.NONDET);
		builder.addDeclaration(auxvarinfo.getVarDec());
		builder.addAuxVar(auxvarinfo);

		// final IdentifierExpression tmpVarIdExpr = new IdentifierExpression(loc, tmpId);
		final Overapprox overAppFlag = new Overapprox(methodName, loc);
		builder.addOverapprox(overAppFlag);
		final RValue lrVal = new RValue(auxvarinfo.getExp(), resultType);
		builder.setLrValue(lrVal);
		return builder.build();
	}

	private Result handleStrChr(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		/*
		 * C11, 7.21.5.2 says: "#include <string.h> char *strchr(const char *s, int c);
		 *
		 * Description: The strchr function locates the first occurrence of c (converted to a char) in the string
		 * pointed to by s. The terminating null character is considered to be part of the string. Returns : The strchr
		 * function returns a pointer to the located character, or a null pointer if the character does not occur in the
		 * string."
		 *
		 * We replace the method call by a fresh char pointer variable which is havocced, and assumed to be either NULL
		 * or a pointer into the area where the argument pointer is valid.
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		// dispatch first argument -- we need its value for the assume

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult argS =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);
		builder.addDeclarations(argS.getDeclarations()).addStatements(argS.getStatements())
				.addOverapprox(argS.getOverapprs()).addAuxVars(argS.getAuxVars())
				.addNeighbourUnionFields(argS.getNeighbourUnionFields());

		// dispatch second argument -- only for its sideeffects
		final ExpressionResult argC =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[1]);
		builder.addDeclarations(argC.getDeclarations()).addStatements(argC.getStatements())
				.addOverapprox(argC.getOverapprs()).addAuxVars(argC.getAuxVars())
				.addNeighbourUnionFields(argC.getNeighbourUnionFields());

		// introduce fresh aux variable
		final CPointer resultType = new CPointer(new CPrimitive(CPrimitives.CHAR));
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.NONDET);
		builder.addDeclaration(auxvarinfo.getVarDec());
		builder.addAuxVar(auxvarinfo);

		final Expression nullExpr = mExpressionTranslation.constructNullPointer(loc);

		/*
		 * if we are in memsafety-mode: add assertions that check that arg_s.lrVal.getValue is a valid pointer
		 *
		 * technical Notes: these assertions are added before the assume statement and before the result can be assigned
		 * thus the overapproximation introduced does not affect violations of these assertions
		 */
		builder.addStatements(
				mMemoryHandler.constructMemsafetyChecksForPointerExpression(loc, argS.getLrValue().getValue()));

		// the havocced/uninitialized variable that represents the return value
		final Expression tmpExpr = auxvarinfo.getExp();// new IdentifierExpression(loc, tmpId);

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
			final Expression equalsNull =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, baseEqualsNull, offsetEqualsNull);
			// old solution did not work quickly..
			// final BinaryExpression equalsNull = expressionTranslation.constructBinaryComparisonExpression(loc,
			// new BinaryExpression(loc, Operator.COMPEQ, tmpExpr, nullExpr);
			// res.base == arg_s.base
			final Expression baseEquals = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_equals, MemoryHandler.getPointerBaseAddress(tmpExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents(),
					MemoryHandler.getPointerBaseAddress(argS.getLrValue().getValue(), loc),
					mExpressionTranslation.getCTypeOfPointerComponents());
			// res.offset >= 0
			final Expression offsetNonNegative = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_lessEqual,
					mTypeSizes.constructLiteralForIntegerType(loc, mExpressionTranslation.getCTypeOfPointerComponents(),
							new BigInteger("0")),
					mExpressionTranslation.getCTypeOfPointerComponents(), MemoryHandler.getPointerOffset(tmpExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents());
			// res.offset < length(arg_s.base)
			final Expression offsetSmallerLength = mExpressionTranslation.constructBinaryComparisonIntegerExpression(
					loc, IASTBinaryExpression.op_lessEqual, MemoryHandler.getPointerOffset(tmpExpr, loc),
					mExpressionTranslation.getCTypeOfPointerComponents(),
					ExpressionFactory.constructNestedArrayAccessExpression(loc, mMemoryHandler.getLengthArray(loc),
							new Expression[] {
									MemoryHandler.getPointerBaseAddress(argS.getLrValue().getValue(), loc) }),
					mExpressionTranslation.getCTypeOfPointerComponents());
			// res.base == arg_s.base && res.offset >= 0 && res.offset <= length(arg_s.base)
			final Expression inRange =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, baseEquals, ExpressionFactory
							.newBinaryExpression(loc, Operator.LOGICAND, offsetNonNegative, offsetSmallerLength));
			// assume equalsNull or inRange
			final AssumeStatement assume = new AssumeStatement(loc,
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, equalsNull, inRange));
			builder.addStatement(assume);
		}

		// final List<Overapprox> overapprox = new ArrayList<>();
		final Overapprox overappFlag = new Overapprox(name, loc);
		// overapprox.add(overappFlag);
		// assume.getPayload().getAnnotations().put(Overapprox.getIdentifier(), overappFlag);
		builder.addOverapprox(overappFlag);

		final RValue lrVal = new RValue(tmpExpr, resultType);
		builder.setLrValue(lrVal);

		return builder.build();
	}

	/**
	 * TOOD pthread support
	 */
	private Result handlePthread_create(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 4, name, arguments);
		final ExpressionResult argThreadIdPointer;
		{
			final ExpressionResult tmp =
					mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);
			// TODO 2018-10-25 Matthias: conversion not correct
			// we do not have a void pointer but a pthread_t pointer
			// but this incorrectness will currently not have a
			// negative effect
			argThreadIdPointer =
					mExprResultTransformer.convert(loc, tmp, new CPointer(new CPrimitive(CPrimitives.VOID)));
		}
		final ExpressionResult argThreadAttributes =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[1]);
		final ExpressionResult argStartRoutine =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[2]);
		final ExpressionResult startRoutineArguments;
		{
			final ExpressionResult tmp =
					mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[3]);
			startRoutineArguments =
					mExprResultTransformer.convert(loc, tmp, new CPointer(new CPrimitive(CPrimitives.VOID)));
		}
		// We hope that the function is not given by a function pointer that is stored
		// in a variable but directly by the function name
		final String rawProcName;
		if (arguments[2] instanceof CASTIdExpression) {
			final CASTIdExpression castIdExpr = (CASTIdExpression) arguments[2];
			rawProcName = castIdExpr.getName().toString();
		} else if (arguments[2] instanceof CASTUnaryExpression) {
			final CASTUnaryExpression castUnaryExpr = (CASTUnaryExpression) arguments[2];
			if (castUnaryExpr.getOperator() == IASTUnaryExpression.op_amper) {
				// function foo is probably given as a function pointer of the form & foo
				if (castUnaryExpr.getOperand() instanceof CASTIdExpression) {
					final CASTIdExpression castIdExpr = (CASTIdExpression) castUnaryExpr.getOperand();
					rawProcName = castIdExpr.getName().toString();
				} else {
					throw new UnsupportedOperationException("Third argument of pthread_create is: "
							+ castUnaryExpr.getOperand().getClass().getSimpleName());
				}
			} else {
				throw new UnsupportedOperationException(
						"Third argument of pthread_create is: " + arguments[2].getClass().getSimpleName());
			}
		} else {
			throw new UnsupportedOperationException(
					"Third argument of pthread_create is " + arguments[2].getClass().getSimpleName());
		}

		final String multiParseProcedureName =
				mSymboltable.applyMultiparseRenaming(node.getContainingFilename(), rawProcName);
		if (!mProcedureManager.hasProcedure(multiParseProcedureName)) {
			throw new UnsupportedOperationException("cannot find function " + multiParseProcedureName
					+ " Ultimate does not support pthread_create in combination with function pointers");
		}

		final IdentifierExpression idExpr = (IdentifierExpression) argStartRoutine.getLrValue().getValue();
		final String prefix = idExpr.getIdentifier().substring(0, 9);
		if (!prefix.equals("#funAddr~")) {
			throw new UnsupportedOperationException("unable to decode " + idExpr.getIdentifier());
		}
		final String methodName = idExpr.getIdentifier().substring(9);

		final HeapLValue heapLValue;
		if (argThreadIdPointer.getLrValue() instanceof HeapLValue) {
			heapLValue = (HeapLValue) argThreadIdPointer.getLrValue();
		} else {
			heapLValue = LRValueFactory.constructHeapLValue(mTypeHandler, argThreadIdPointer.getLrValue().getValue(),
					argThreadIdPointer.getLrValue().getCType(), false, null);
		}

		final Expression threadId = mTypeSizes.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.ULONG),
				BigInteger.valueOf(mPthreadCreateCounter++));
		final List<Statement> writeCall =
				mMemoryHandler.getWriteCall(loc, heapLValue, threadId, new CPrimitive(CPrimitives.ULONG), false, node);

		final CFunction function = mProcedureManager.getCFunctionType(methodName);
		final int params = function.getParameterTypes().length;
		final Expression[] forkArguments;
		if (params == 0) {
			forkArguments = new Expression[0];
		} else if (params == 1) {
			forkArguments = new Expression[] { startRoutineArguments.getLrValue().getValue() };
		} else {
			throw new UnsupportedSyntaxException(loc, "pthread_create calls function with more than one argument");
		}
		final ForkStatement fs = new ForkStatement(loc, new Expression[] { threadId }, methodName, forkArguments);
		mProcedureManager.registerForkStatement(fs);

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAllExceptLrValue(argThreadIdPointer, argThreadAttributes, argStartRoutine, startRoutineArguments);
		builder.addStatements(writeCall);

		final boolean letPthreadCreateAlwaysReturnZero = false;
		final CPrimitive returnValueCType = new CPrimitive(CPrimitive.CPrimitives.INT);
		final Expression returnValue;
		if (letPthreadCreateAlwaysReturnZero) {
			returnValue = mTypeSizes.constructLiteralForIntegerType(loc, returnValueCType, BigInteger.ZERO);
		} else {
			// auxvar for fork return value (status code)
			final AuxVarInfo auxvarinfo =
					mAuxVarInfoBuilder.constructAuxVarInfo(loc, returnValueCType, SFO.AUXVAR.NONDET);
			builder.addDeclaration(auxvarinfo.getVarDec());
			builder.addAuxVar(auxvarinfo);
			returnValue = auxvarinfo.getExp();
		}
		final LRValue val = new RValue(returnValue, returnValueCType);

		builder.setLrValue(val);
		builder.addStatement(fs);
		return builder.build();
	}

	/**
	 * TOOD pthread support
	 */
	private Result handlePthread_join(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		// get arguments
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);
		final ExpressionResult argThreadId;
		{
			final ExpressionResult tmp =
					mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);
			// TODO 2018-10-26 Matthias: we presume that pthread_t is unsigned long
			argThreadId = mExprResultTransformer.convert(loc, tmp, new CPrimitive(CPrimitives.ULONG));
		}
		final ExpressionResult argAddressOfResultPointer;
		{
			// final ExpressionResult tmp = mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main,
			// loc,
			// arguments[1]);
			final ExpressionResult tmp = (ExpressionResult) main.dispatch(arguments[1]);
			argAddressOfResultPointer =
					mExprResultTransformer.convert(loc, tmp, new CPointer(new CPrimitive(CPrimitives.VOID)));
		}

		// Object that will build our result
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAllExceptLrValue(argThreadId, argAddressOfResultPointer);

		final JoinStatement js;
		if (argAddressOfResultPointer.getLrValue().isNullPointerConstant()) {
			js = new JoinStatement(loc, new Expression[] { argThreadId.getLrValue().getValue() }, new VariableLHS[0]);
			builder.addStatement(js);
		} else {
			// auxvar for joined procedure's return value
			final CType cType = new CPointer(new CPrimitive(CPrimitives.VOID));
			final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.NONDET);
			builder.addDeclaration(auxvarinfo.getVarDec());
			builder.addAuxVar(auxvarinfo);
			js = new JoinStatement(loc, new Expression[] { argThreadId.getLrValue().getValue() },
					new VariableLHS[] { auxvarinfo.getLhs() });
			builder.addStatement(js);
			final HeapLValue heapLValue;
			if (argAddressOfResultPointer.getLrValue() instanceof HeapLValue) {
				heapLValue = (HeapLValue) argAddressOfResultPointer.getLrValue();
			} else {
				heapLValue = LRValueFactory.constructHeapLValue(mTypeHandler,
						argAddressOfResultPointer.getLrValue().getValue(), cType, false, null);
			}
			final List<Statement> wc =
					mMemoryHandler.getWriteCall(loc, heapLValue, auxvarinfo.getExp(), cType, false, node);
			builder.addStatements(wc);
		}
		// we assume that this function is always successful and returns 0
		builder.setLrValue(new RValue(
				mTypeSizes.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT), BigInteger.ZERO),
				new CPrimitive(CPrimitives.INT)));
		return builder.build();
	}

	private Result handlePthread_exit(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		mMemoryHandler.requireMemoryModelFeature(MemoryModelDeclarations.Ultimate_Pthreads_Mutex);

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);

		final ExpressionResult arg =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);
		final ExpressionResult transformedArg =
				mExprResultTransformer.convert(loc, arg, new CPointer(new CPrimitive(CPrimitives.VOID)));

		final IBoogieType type = mTypeHandler.getBoogiePointerType();
		final String identifier = SFO.RES;
		final DeclarationInformation declarationInformation = new DeclarationInformation(
				StorageClass.IMPLEMENTATION_OUTPARAM, mProcedureManager.getCurrentProcedureID());
		final LeftHandSide[] lhs =
				new LeftHandSide[] { new VariableLHS(loc, type, identifier, declarationInformation) };
		final AssignmentStatement retValAssignment =
				new AssignmentStatement(loc, lhs, new Expression[] { transformedArg.getLrValue().getValue() });
		final ExpressionResultBuilder erb = new ExpressionResultBuilder();
		erb.addAllExceptLrValue(transformedArg);
		erb.addStatement(retValAssignment);
		erb.addStatement(new ReturnStatement(loc));

		return erb.build();
	}

	/**
	 * We assume that the mutex type is PTHREAD_MUTEX_NORMAL which means that if we lock a mutex that that is already
	 * locked, then the thread blocks.
	 */
	private Result handlePthread_mutex_lock(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);

		final ExpressionResult arg =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);

		// final CPrimitive returnType = new CPrimitive(CPrimitives.INT);
		// // we assume that function is always successful and returns 0
		// final BigInteger value = BigInteger.ZERO;
		// final Expression mutexArray = mMemoryHandler.constructMutexArrayIdentifierExpression(loc);
		// final Expression mutexArrayAtIndex = ExpressionFactory.constructNestedArrayAccessExpression(loc, mutexArray,
		// new Expression[] { arg.getLrValue().getValue() });
		// final Expression mutexIsUnlocked = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ,
		// mutexArrayAtIndex, mMemoryHandler.getBooleanArrayHelper().constructValue(false));
		// final AssumeStatement assumeMutexUnlocked = new AssumeStatement(loc, mutexIsUnlocked);
		final Expression index = arg.getLrValue().getValue();
		// final AssignmentStatement lockMutex = mMemoryHandler.constructMutexArrayAssignment(loc, index, true);
		final ExpressionResultBuilder erb = new ExpressionResultBuilder();
		// auxvar for joined procedure's return value
		final CType cType = new CPrimitive(CPrimitives.INT);
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.NONDET);
		erb.addDeclaration(auxvarinfo.getVarDec());
		erb.addAuxVar(auxvarinfo);
		erb.addStatement(mMemoryHandler.constructPthreadMutexLockCall(loc, index, auxvarinfo.getLhs()));
		erb.setLrValue(new RValue(auxvarinfo.getExp(), new CPrimitive(CPrimitives.INT)));
		// erb.addAllExceptLrValue(arg);
		// erb.addStatement(assumeMutexUnlocked);
		// erb.addStatement(lockMutex);
		// erb.setLrValue(new RValue(mTypeSizes.constructLiteralForIntegerType(loc, returnType, value),
		// new CPrimitive(CPrimitives.INT)));
		return erb.build();
	}

	/**
	 * We assume that the mutex type is PTHREAD_MUTEX_NORMAL which means that if we unlock a mutex that has never been
	 * locked, the behavior is undefined. We use a semantics where unlocking a non-locked mutex is a no-op. For the
	 * return value we follow what GCC did in my experiments. It produced code that returned 0 even if we unlocked a
	 * non-locked mutex.
	 */
	private Result handlePthread_mutex_unlock(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		mMemoryHandler.requireMemoryModelFeature(MemoryModelDeclarations.Ultimate_Pthreads_Mutex);

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);

		final ExpressionResult arg =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);

		final CPrimitive returnType = new CPrimitive(CPrimitives.INT);
		// we assume that function is always successful and returns 0
		final BigInteger value = BigInteger.ZERO;
		final Expression index = arg.getLrValue().getValue();
		final AssignmentStatement unlockMutex = mMemoryHandler.constructMutexArrayAssignment(loc, index, false);
		final ExpressionResultBuilder erb = new ExpressionResultBuilder();
		erb.addAllExceptLrValue(arg);
		erb.addStatement(unlockMutex);
		erb.setLrValue(new RValue(mTypeSizes.constructLiteralForIntegerType(loc, returnType, value),
				new CPrimitive(CPrimitives.INT)));
		return erb.build();
	}

	private Result handlePthread_mutex_init(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		mMemoryHandler.requireMemoryModelFeature(MemoryModelDeclarations.Ultimate_Pthreads_Mutex);

		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);

		final ExpressionResult arg1 =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);
		final ExpressionResult arg2 =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[1]);
		final boolean isNullPointerLiteral = mMemoryHandler.isNullPointerLiteral(arg2.getLrValue().getValue());
		if (!isNullPointerLiteral) {
			final String msg = "The second argument of the pthread_mutex_init is not a null pointer. This means that "
					+ "non-default attributes are used. We support only the default attributes.";
			throw new UnsupportedSyntaxException(loc, msg);
		}

		final CPrimitive returnType = new CPrimitive(CPrimitives.INT);
		// we assume that function is always successful and returns 0
		final BigInteger value = BigInteger.ZERO;
		final Expression index = arg1.getLrValue().getValue();
		final AssignmentStatement unlockMutex = mMemoryHandler.constructMutexArrayAssignment(loc, index, false);
		final ExpressionResultBuilder erb = new ExpressionResultBuilder();
		erb.addAllExceptLrValue(arg1);
		erb.addStatement(unlockMutex);
		erb.setLrValue(new RValue(mTypeSizes.constructLiteralForIntegerType(loc, returnType, value),
				new CPrimitive(CPrimitives.INT)));
		return erb.build();
	}

	private static Result handleBuiltinUnreachable(final ILocation loc) {
		/*
		 * https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html
		 *
		 * Built-in Function: void __builtin_unreachable (void)
		 *
		 * If control flow reaches the point of the __builtin_unreachable, the program is undefined. It is useful in
		 * situations where the compiler cannot deduce the unreachability of the code.
		 */

		// TODO: Add option that allows us to check for builtin_unreachable by adding assert
		// return new ExpressionResult(Collections.singletonList(new AssertStatement(loc,
		// new de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral(loc, false))), null);
		// TODO: Add option that just ignores the function:
		// return new SkipResult();
		// TODO: Keep the following code, but add it as option together with the other two
		return new ExpressionResult(
				Collections.singletonList(new AssumeStatement(loc, ExpressionFactory.createBooleanLiteral(loc, false))),
				null);
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
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);
		final ExpressionResult convertedArgument =
				mExpressionTranslation.convertIfNecessary(loc, decayedArgument, new CPrimitive(CPrimitives.INT));
		final ExpressionResult arg = convertedArgument;

		final RValue rvalue = mExpressionTranslation.constructBuiltinFesetround(loc, (RValue) arg.getLrValue());

		return new ExpressionResultBuilder().setLrValue(rvalue).build();

	}

	private Result handleMemset(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		/*
		 * C11 says in 7.24.6.1 void *memset(void *s, int c, size_t n); The memset function copies the value of c
		 * (converted to an unsigned char) into each of the first n characters of the object pointed to by s.
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 3, name, arguments);

		final ExpressionResult dispatchedArgS =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);
		final ExpressionResult dispatchedArgC =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[1]);
		final ExpressionResult dispatchedArgN =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[2]);

		// TODO: No conversion for ArgS?
		final ExpressionResult convertedArgC =
				mExpressionTranslation.convertIntToInt(loc, dispatchedArgC, new CPrimitive(CPrimitives.INT));
		final ExpressionResult convertedArgN =
				mExpressionTranslation.convertIntToInt(loc, dispatchedArgN, mTypeSizeComputer.getSizeT());

		final ExpressionResultBuilder result = new ExpressionResultBuilder().setLrValue(dispatchedArgS.getLrValue());

		result.addAllExceptLrValue(dispatchedArgS);
		result.addAllExceptLrValue(convertedArgC);
		result.addAllExceptLrValue(convertedArgN);

		final CPointer voidPointerType = new CPointer(new CPrimitive(CPrimitives.VOID));
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, voidPointerType, SFO.AUXVAR.MEMSETRES);
		result.addDeclaration(auxvar.getVarDec());
		result.addAuxVar(auxvar);

		result.addStatement(mMemoryHandler.constructUltimateMemsetCall(loc, dispatchedArgS.getLrValue().getValue(),
				convertedArgC.getLrValue().getValue(), convertedArgN.getLrValue().getValue(), auxvar.getLhs()));
		return result.build();
	}

	private Result handleCalloc(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		/*
		 * C11 says in 7.22.3.2 void *calloc(size_t nmemb, size_t size); The calloc function allocates space for an
		 * array of nmemb objects, each of whose size is size. The space is initialized to all bits zero.
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 2, name, arguments);

		final ExpressionResult nmemb = mExprResultTransformer.dispatchDecaySwitchToRValueConvertFunctionArgument(main,
				loc, arguments[0], mTypeSizeComputer.getSizeT());
		final ExpressionResult size = mExprResultTransformer.dispatchDecaySwitchToRValueConvertFunctionArgument(main,
				loc, arguments[1], mTypeSizeComputer.getSizeT());

		final Expression product = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_multiply, nmemb.getLrValue().getValue(), mTypeSizeComputer.getSizeT(),
				size.getLrValue().getValue(), mTypeSizeComputer.getSizeT());
		final ExpressionResultBuilder result = new ExpressionResultBuilder().addAllExceptLrValue(nmemb, size);

		final CPointer resultType = new CPointer(new CPrimitive(CPrimitives.VOID));
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.MALLOC);
		result.addDeclaration(auxvar.getVarDec());
		result.addStatement(mMemoryHandler.getMallocCall(product, auxvar.getLhs(), loc));
		result.addStatement(mMemoryHandler.constructUltimateMeminitCall(loc, nmemb.getLrValue().getValue(),
				size.getLrValue().getValue(), product, auxvar.getExp()));
		result.setLrValue(new RValue(auxvar.getExp(), resultType));
		return result.build();
	}

	/**
	 * Translates free(e) by creating a function call expression for the ~free(e) function and declaring its usage in
	 * the memory model.
	 */
	private Result handleFree(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, name, arguments);

		final ExpressionResult pRex =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);

		final ExpressionResultBuilder resultBuilder =
				new ExpressionResultBuilder().addAllExceptLrValue(pRex).setLrValue(pRex.getLrValue());

		/*
		 * Add checks for validity of the to be freed pointer if required.
		 */
		resultBuilder.addStatements(mMemoryHandler.getChecksForFreeCall(loc, (RValue) pRex.getLrValue()));

		/*
		 * Add a call to our internal deallocation procedure Ultimate.dealloc
		 */
		final CallStatement deallocCall = mMemoryHandler.getDeallocCall(pRex.getLrValue(), loc);
		resultBuilder.addStatement(deallocCall);

		return resultBuilder.build();
	}

	private Result handleAlloc(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String methodName) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, methodName, arguments);

		final ExpressionResult exprRes =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);
		final ExpressionResult exprResConverted =
				mExprResultTransformer.convert(loc, exprRes, mTypeSizeComputer.getSizeT());
		final ExpressionResultBuilder erb = new ExpressionResultBuilder().addAllExceptLrValue(exprResConverted);
		final CPointer resultType = new CPointer(new CPrimitive(CPrimitives.VOID));
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.MALLOC);
		erb.addDeclaration(auxvar.getVarDec());
		erb.addStatement(mMemoryHandler.getMallocCall(exprRes.getLrValue().getValue(), auxvar.getLhs(), loc));
		erb.setLrValue(new RValue(auxvar.getExp(), resultType));

		// for alloc a we have to free the variable ourselves when the
		// stackframe is closed, i.e. at a return
		if ("alloca".equals(methodName) || "__builtin_alloca".equals(methodName)) {
			final LocalLValue llVal = new LocalLValue(auxvar.getLhs(), resultType, null);
			mMemoryHandler.addVariableToBeFreed(
					new LocalLValueILocationPair(llVal, LocationFactory.createIgnoreLocation(loc)));
			// we need to clear auxVars because otherwise the malloc auxvar is havocced after
			// this, and free (triggered by the statement before) would fail.
			erb.clearAuxVars();
		}
		return erb.build();
	}

	private Result handleBuiltinExpect(final IDispatcher main, final IASTFunctionCallExpression node,
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
		final ExpressionResult arg1 =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);
		final ExpressionResult arg2 =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[1]);
		return new ExpressionResultBuilder().addAllExceptLrValue(arg1, arg2).setLrValue(arg1.getLrValue()).build();
	}

	private static ExpressionResult handleAbort(final ILocation loc) {
		return new ExpressionResult(
				Collections.singletonList(new AssumeStatement(loc, ExpressionFactory.createBooleanLiteral(loc, false))),
				null);
	}

	private Result handleVerifierNonDet(final IDispatcher main, final ILocation loc, final CType cType) {
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.NONDET);
		resultBuilder.addDeclaration(auxvarinfo.getVarDec());
		resultBuilder.addAuxVar(auxvarinfo);

		final LRValue returnValue = new RValue(auxvarinfo.getExp(), cType);
		resultBuilder.setLrValue(returnValue);
		mExpressionTranslation.addAssumeValueInRangeStatements(loc, returnValue.getValue(), returnValue.getCType(),
				resultBuilder);

		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, resultBuilder.getDeclarations(),
				resultBuilder.getAuxVars());
		return resultBuilder.build();
	}

	private Result handleRand(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		checkArguments(loc, 0, name, node);

		final CPrimitive cType = new CPrimitive(CPrimitives.INT);
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.NONDET);
		resultBuilder.addDeclaration(auxvarinfo.getVarDec());
		resultBuilder.addAuxVar(auxvarinfo);

		final LRValue returnValue = new RValue(auxvarinfo.getExp(), cType);
		resultBuilder.setLrValue(returnValue);

		final Expression expr = returnValue.getValue();
		final Expression minValue = mTypeSizes.constructLiteralForIntegerType(loc, cType, BigInteger.ZERO);
		final Expression maxValue =
				mTypeSizes.constructLiteralForIntegerType(loc, cType, mTypeSizes.getMaxValueOfPrimitiveType(cType));

		final Expression biggerMinInt = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, minValue, cType, expr, cType);
		final Expression smallerMaxValue = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, expr, cType, maxValue, cType);
		final AssumeStatement inRange = new AssumeStatement(loc, ExpressionFactory.newBinaryExpression(loc,
				BinaryExpression.Operator.LOGICAND, biggerMinInt, smallerMaxValue));
		resultBuilder.addStatement(inRange);

		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, resultBuilder.getDeclarations(),
				resultBuilder.getAuxVars());
		return resultBuilder.build();
	}

	private Result handleVerifierAssume(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		// according to SV-Comp specification assume takes only one argument, but the code allows more than one
		checkArguments(loc, 1, name, node.getArguments());

		final List<Expression> args = new ArrayList<>();
		final List<ExpressionResult> results = new ArrayList<>();
		for (final IASTInitializerClause inParam : node.getArguments()) {
			ExpressionResult in =
					mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, inParam);
			if (in.getLrValue().getValue() == null) {
				final String msg = "Incorrect or invalid in-parameter! " + loc.toString();
				throw new IncorrectSyntaxException(loc, msg);
			}
			in = mExprResultTransformer.rexIntToBoolIfNecessary(in, loc);
			args.add(in.getLrValue().getValue());
			results.add(in);
		}

		final ExpressionResultBuilder rtr = new ExpressionResultBuilder().addAllExceptLrValue(results);
		for (final Expression a : args) {
			// could just take the first as there is only one, but it's so easy to make it more general..
			rtr.addStatement(new AssumeStatement(loc, a));
		}
		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, rtr.getDeclarations(), rtr.getAuxVars());
		return rtr.build();
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
					mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, argument);
			final ExpressionResult convertedArgument =
					mExpressionTranslation.convertIfNecessary(loc, decayedArgument, floatFunction.getType());
			rtr.add(convertedArgument);
		}

		final CPrimitive typeDeterminedByName = floatFunction.getType();
		if (typeDeterminedByName != null) {
			for (final ExpressionResult arg : rtr) {
				mExpressionTranslation.convertFloatToFloat(loc, arg, typeDeterminedByName);
			}

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
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);
		final ExpressionResult rr =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[1]);

		// Note: this works because SMTLIB already ensures that all comparisons return false if one of the arguments is
		// NaN

		return mCHandler.handleRelationalOperators(loc, op, rl, rr);
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
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);
		final ExpressionResult rightRvaluedResult =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[1]);
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
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[0]);
		ExpressionResult rightOp =
				mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arguments[1]);
		final Pair<ExpressionResult, ExpressionResult> newOps =
				mExpressionTranslation.usualArithmeticConversions(loc, leftOp, rightOp);
		leftOp = newOps.getFirst();
		rightOp = newOps.getSecond();

		final ExpressionResult lessThan =
				mCHandler.handleRelationalOperators(loc, IASTBinaryExpression.op_lessThan, leftOp, rightOp);
		final ExpressionResult greaterThan =
				mCHandler.handleRelationalOperators(loc, IASTBinaryExpression.op_greaterThan, leftOp, rightOp);

		final Expression expr = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
				lessThan.getLrValue().getValue(), greaterThan.getLrValue().getValue());
		final LRValue lrVal = new RValue(expr, new CPrimitive(CPrimitives.INT), true);
		final ExpressionResult rtr =
				new ExpressionResultBuilder().addAllExceptLrValue(lessThan, greaterThan).setLrValue(lrVal).build();
		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, rtr.getDeclarations(), rtr.getAuxVars());
		return rtr;
	}

	private Result handleBuiltinObjectSize(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		// DD: builtin-object size is way more complicated that the old implementation!
		// Read https://gcc.gnu.org/onlinedocs/gcc/Object-Size-Checking.html
		// For testing, overapproximate and do not dispatch arguments (I understand the spec as this is whats happening,
		// but I am not sure)
		return handleByOverapproximationWithoutDispatch(main, node, loc, name, 2, new CPrimitive(CPrimitives.INT));
		// main.warn(loc, "used trivial implementation of __builtin_object_size");
		// final CPrimitive cType = new CPrimitive(CPrimitives.INT);
		// final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(loc, cType, BigInteger.ZERO);
		// return new ExpressionResult(new RValue(zero, cType));
	}

	private Result handlePrintF(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc) {
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		// 2015-11-05 Matthias: TODO check if int is reasonable here
		final AuxVarInfo auxvarinfo =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, new CPrimitive(CPrimitives.INT), SFO.AUXVAR.NONDET);
		resultBuilder.addDeclaration(auxvarinfo.getVarDec());
		resultBuilder.addStatement(new HavocStatement(loc, new VariableLHS[] { auxvarinfo.getLhs() }));

		final LRValue returnValue = new RValue(auxvarinfo.getExp(), null);
		resultBuilder.setLrValue(returnValue);

		// dispatch all arguments
		for (final IASTInitializerClause arg : node.getArguments()) {
			final ExpressionResult argRes =
					mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main, loc, arg);
			resultBuilder.addAllExceptLrValue(argRes);
		}

		return resultBuilder.build();
	}

	private Result handleMemcpy(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		return handleMemCopyOrMove(main, node, loc, name, SFO.AUXVAR.MEMCPYRES, MemoryModelDeclarations.C_Memcpy);
	}

	private Result handleMemmove(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		return handleMemCopyOrMove(main, node, loc, name, SFO.AUXVAR.MEMMOVERES, MemoryModelDeclarations.C_Memmove);
	}

	private Result handleMemCopyOrMove(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final AUXVAR auxVar, final MemoryModelDeclarations mmDecl) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 3, name, arguments);
		final CPointer voidType = new CPointer(new CPrimitive(CPrimitives.VOID));
		final ExpressionResult dest = mExprResultTransformer.dispatchDecaySwitchToRValueConvertFunctionArgument(main,
				loc, arguments[0], voidType);
		final ExpressionResult src = mExprResultTransformer.dispatchDecaySwitchToRValueConvertFunctionArgument(main,
				loc, arguments[1], voidType);
		final ExpressionResult size = mExprResultTransformer.dispatchDecaySwitchToRValueConvertFunctionArgument(main,
				loc, arguments[2], mTypeSizeComputer.getSizeT());

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		resultBuilder.addAllExceptLrValue(dest);
		resultBuilder.addAllExceptLrValue(src);
		resultBuilder.addAllExceptLrValue(size);

		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, dest.getLrValue().getCType(), auxVar);

		final CallStatement call = StatementFactory.constructCallStatement(loc, false,
				new VariableLHS[] { auxvarinfo.getLhs() }, mmDecl.getName(), new Expression[] {
						dest.getLrValue().getValue(), src.getLrValue().getValue(), size.getLrValue().getValue() });
		resultBuilder.addDeclaration(auxvarinfo.getVarDec());
		resultBuilder.addAuxVar(auxvarinfo);
		resultBuilder.addStatement(call);
		resultBuilder.setLrValue(new RValue(auxvarinfo.getExp(), new CPointer(new CPrimitive(CPrimitives.VOID))));

		// add marker for global declaration to memory handler
		mMemoryHandler.requireMemoryModelFeature(mmDecl);

		// add required information to function handler.
		mProcedureManager.registerProcedure(mmDecl.getName());
		// mProcedureManager.registerCall(mmDecl.getName());

		return resultBuilder.build();
	}

	private Result handleErrorFunction(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc) {
		final boolean checkSvcompErrorfunction = mSettings.checkSvcompErrorFunction();
		final Expression falseLiteral = ExpressionFactory.createBooleanLiteral(loc, false);
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

	private static Result handleLtlStep(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc) {
		final LTLStepAnnotation ltlStep = new LTLStepAnnotation();
		final AssumeStatement assumeStmt = new AssumeStatement(loc, ExpressionFactory.createBooleanLiteral(loc, true));
		ltlStep.annotate(assumeStmt);
		return new ExpressionResult(Collections.singletonList(assumeStmt), null);
	}

	private Result handleByIgnore(final IDispatcher main, final ILocation loc, final String methodName) {
		mReporter.warn(loc, "ignored call to " + methodName);
		return new SkipResult();
	}

	private static Result handleByUnsupportedSyntaxException(final ILocation loc, final String functionName) {
		throw new UnsupportedSyntaxException(loc, "Unsupported function: " + functionName);
	}

	private static Result handleByUnsupportedSyntaxExceptionKnown(final ILocation loc, final String lib,
			final String functionName) {
		throw new UnsupportedSyntaxException(loc, "Unsupported function from " + lib + ": " + functionName);
	}

	/**
	 * Handle a function call by dispatching all arguments and then calling a function with no arguments that has the
	 * name of the function and is marked with the {@link Overapprox} annotation.
	 *
	 * @param main
	 *            the current dispatcher
	 * @param node
	 *            the function call expression
	 * @param loc
	 *            the location of the call
	 * @param methodName
	 *            the name of the method
	 * @param numberOfArgs
	 *            the number of arguments
	 * @param resultType
	 *            the return type
	 * @return An {@link ExpressionResult} representing the effect of the call
	 */
	private Result handleByOverapproximation(final IDispatcher main, final IASTFunctionCallExpression node,
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
		return new ExpressionResultBuilder().addAllExceptLrValue(results).setLrValue(overapproxCall.getLrValue())
				.build();
	}

	/**
	 * We handle a function call by dispatching all arguments, but we then ignore the call completely.
	 *
	 * Useful for void functions that do nothing.
	 */
	private Result handleVoidFunctionBySkipAndDispatch(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String methodName, final int numberOfArgs) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, numberOfArgs, methodName, arguments);
		final List<ExpressionResult> results = new ArrayList<>();
		for (final IASTInitializerClause argument : arguments) {
			results.add((ExpressionResult) main.dispatch(argument));
		}
		return new ExpressionResultBuilder().addAllExceptLrValue(results).build();
	}

	private Result handleByOverapproximationWithoutDispatch(final IDispatcher main,
			final IASTFunctionCallExpression node, final ILocation loc, final String methodName, final int numberOfArgs,
			final CType resultType) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, numberOfArgs, methodName, arguments);
		return constructOverapproximationForFunctionCall(main, loc, methodName, resultType);
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
	private ExpressionResult constructOverapproximationForFunctionCall(final IDispatcher main, final ILocation loc,
			final String functionName, final CType resultType) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		// introduce fresh aux variable
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.NONDET);
		builder.addDeclaration(auxvar.getVarDec());
		builder.addAuxVar(auxvar);
		builder.addOverapprox(new Overapprox(functionName, loc));
		builder.setLrValue(new RValue(auxvar.getExp(), resultType));
		return builder.build();
	}

	private static void checkArguments(final ILocation loc, final int expectedArgs, final String name,
			final IASTInitializerClause[] arguments) {
		if (arguments.length != expectedArgs) {
			throw new IncorrectSyntaxException(loc, name + " is expected to have " + expectedArgs
					+ " arguments, but was called with " + arguments.length);
		}
	}

	private static void checkArguments(final ILocation loc, final int expectedArgs, final String name,
			final IASTFunctionCallExpression call) {
		checkArguments(loc, 0, name, call.getArguments());
	}

	private static <K, V> void fill(final Map<K, V> map, final K key, final V value) {
		final V old = map.put(key, value);
		if (old != null) {
			throw new AssertionError("Accidentally overwrote definition for " + key);
		}
	}

	private ILocation getLoc(final IDispatcher main, final IASTFunctionCallExpression node) {
		if (mSettings.isSvcompMode()) {
			return mLocationFactory.createCLocation(node, new Check(Check.Spec.PRE_CONDITION));
		}
		return mLocationFactory.createCLocation(node);
	}

	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	@FunctionalInterface
	private interface IFunctionModelHandler {
		Result handleFunction(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
				String methodName);
	}
}
