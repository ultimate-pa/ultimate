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
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryArea;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;

/**
 * Model of stdlib.h (C11, https://en.cppreference.com/w/c/header/stdlib).
 */
public class StdlibLibraryModel implements ILibraryModel {
	private final FunctionModelHelper mHelper;
	private final ExpressionResultTransformer mExprResultTransformer;
	private final TypeSizes mTypeSizes;
	private final TypeSizeAndOffsetComputer mTypeSizeComputer;
	private final ExpressionTranslation mExpressionTranslation;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final MemoryHandler mMemoryHandler;
	private final ProcedureManager mProcedureManager;
	private final INameHandler mNameHandler;
	private final CheckMode mOverflowCheckMode;

	public StdlibLibraryModel(final FunctionModelHelper helper, final ExpressionResultTransformer exprResultTransformer,
			final TypeSizes typeSizes, final TypeSizeAndOffsetComputer typeSizeComputer,
			final ExpressionTranslation expressionTranslation, final AuxVarInfoBuilder auxVarInfoBuilder,
			final MemoryHandler memoryHandler, final ProcedureManager procedureManager, final INameHandler nameHandler,
			final CheckMode overflowCheckMode) {
		mHelper = helper;
		mExprResultTransformer = exprResultTransformer;
		mTypeSizes = typeSizes;
		mTypeSizeComputer = typeSizeComputer;
		mExpressionTranslation = expressionTranslation;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mMemoryHandler = memoryHandler;
		mProcedureManager = procedureManager;
		mNameHandler = nameHandler;
		mOverflowCheckMode = overflowCheckMode;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();

		/**
		 * 7.22.3 Memory management functions
		 *
		 * 7.22.3.2 The calloc function, 7.22.3.3 The free function, 7.22.3.4 The malloc function, 7.22.3.5 The realloc
		 * function
		 */
		result.add(new FunctionModel("calloc", this::handleCalloc));
		result.add(new FunctionModel("free", this::handleFree));
		result.add(new FunctionModel("malloc", this::handleMalloc));
		result.add(new FunctionModel("realloc", this::handleRealloc));

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
		result.add(new FunctionModel("atof", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 1, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("atoi", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 1, new CPrimitive(CPrimitives.INT))));
		result.add(new FunctionModel("atol", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 1, new CPrimitive(CPrimitives.LONG))));
		result.add(new FunctionModel("atoll", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 1, new CPrimitive(CPrimitives.LONGLONG))));

		/**
		 * @formatter:off
		 * 7.22.4 Communication with the environment
		 *
		 * 7.22.4.1 The abort function
		 *   see https://en.cppreference.com/w/c/program/abort
		 * 7.22.4.4 The exit function
		 *   see https://en.cppreference.com/w/c/program/exit
		 * 7.22.4.6 The getenv function
		 * @formatter:on
		 */
		result.add(new FunctionModel("abort", (main, node, loc, name) -> handleAbort(loc)));
		result.add(new FunctionModel("exit", (main, node, loc, name) -> handleAbort(loc)));
		result.add(new FunctionModel("getenv", (main, node, loc, name) -> handleGetenv(main, node, loc)));

		/**
		 * @formatter:off
		 * 7.22.5 Searching and sorting utilities
		 * 7.22.5.2 The qsort function
		 * void qsort( void *ptr, size_t count, size_t size, int (*comp)(const void *, const void *) ));
		 * @formatter:on
		 */
		result.add(new FunctionModel("qsort", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 4, CPointer.voidPointer())));

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
		result.add(new FunctionModel("rand", this::handleRand));

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
		result.add(new FunctionModel("srand",
				(main, node, loc, name) -> mHelper.handleVoidFunctionBySkipAndDispatch(main, node, loc, name, 1)));

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
		result.add(new FunctionModel("strtof", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 2, new CPrimitive(CPrimitives.FLOAT))));
		result.add(new FunctionModel("strtod", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 2, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("strtold", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 2, new CPrimitive(CPrimitives.LONGDOUBLE))));

		/**
		 * 7.22.1.4 The strtol, strtoll, strtoul, and strtoull functions
		 *
		 * see https://en.cppreference.com/w/c/string/byte/strtoul
		 *
		 * Interprets an unsigned integer value in a byte string pointed to by str.
		 *
		 * We handle this by overapproximation and do not check of range errors.
		 *
		 */
		result.add(new FunctionModel("strtol", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 3, new CPrimitive(CPrimitives.LONG))));
		result.add(new FunctionModel("strtoll", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 3, new CPrimitive(CPrimitives.LONGLONG))));
		result.add(new FunctionModel("strtoul", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 3, new CPrimitive(CPrimitives.ULONG))));
		result.add(new FunctionModel("strtoull", (main, node, loc, name) -> mHelper.handleByOverapproximation(main,
				node, loc, name, 3, new CPrimitive(CPrimitives.ULONGLONG))));

		/**
		 * @formatter:off
		 * 7.22.6 Integer arithmetic functions
		 *
		 * 7.22.6.1 The abs, labs and llabs functions
		 * 7.22.6.2 The div, ldiv, and lldiv functions
		 * @formatter:on
		 */
		result.add(new FunctionModel("abs",
				(main, node, loc, name) -> handleAbs(main, node, loc, name, new CPrimitive(CPrimitives.INT))));
		result.add(new FunctionModel("labs",
				(main, node, loc, name) -> handleAbs(main, node, loc, name, new CPrimitive(CPrimitives.LONG))));
		result.add(new FunctionModel("llabs",
				(main, node, loc, name) -> handleAbs(main, node, loc, name, new CPrimitive(CPrimitives.LONGLONG))));
		result.add(new FunctionModel("imaxabs",
				(main, node, loc, name) -> handleAbs(main, node, loc, name, new CPrimitive(CPrimitives.LONGLONG))));

		return result;
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return List.of("aligned_alloc", "atexit", "at_quick_exit", "_Exit", "quick_exit", "system", "bsearch", "mblen",
				"mbtowc", "wctomb", "mbstowcs", "wcstombs", "div", "ldiv", "lldiv");
	}

	private Result handleGetenv(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc) {
		final var builder = new ExpressionResultBuilder();

		// dispatch the argument (unless it's a string literal, then we don't need it)
		assert node.getArguments().length == 1 : "unexpected number of arguments to getenv";
		final var arg = node.getArguments()[0];
		if (!mHelper.isStringLiteral(arg)) {
			final var argRes = (ExpressionResult) main.dispatch(arg);
			builder.addAllExceptLrValue(argRes);
		}

		final var nondetString = mHelper.getNondetStringOrNull(loc);
		builder.addAllExceptLrValue(nondetString).setLrValue(nondetString.getLrValue());

		return builder.build();
	}

	private static ExpressionResult handleAbort(final ILocation loc) {
		return new ExpressionResult(
				Collections.singletonList(new AssumeStatement(loc, ExpressionFactory.createBooleanLiteral(loc, false))),
				null);
	}

	private Result handleCalloc(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		/*
		 * C11 says in 7.22.3.2 void *calloc(size_t nmemb, size_t size); The calloc function allocates space for an
		 * array of nmemb objects, each of whose size is size. The space is initialized to all bits zero.
		 */
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 2, name, arguments);

		final ExpressionResult nmemb = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc,
				arguments[0], mTypeSizeComputer.getSizeT());
		final ExpressionResult size = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc,
				arguments[1], mTypeSizeComputer.getSizeT());

		final Expression product = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_multiply, nmemb.getLrValue().getValue(), mTypeSizeComputer.getSizeT(),
				size.getLrValue().getValue(), mTypeSizeComputer.getSizeT());
		final ExpressionResultBuilder result = new ExpressionResultBuilder().addAllExceptLrValue(nmemb, size);

		final CPointer resultType = CPointer.voidPointer();
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.MALLOC);
		result.addAuxVarWithDeclaration(auxvar);
		result.addStatement(mMemoryHandler.getUltimateMemAllocCall(product, auxvar.getLhs(), loc, MemoryArea.HEAP));
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
		mHelper.checkArguments(loc, 1, name, arguments);

		final ExpressionResult pRex =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);

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

	/**
	 *
	 * signature: void *realloc(void *ptr, size_t size);
	 *
	 * for reference: C11 7.22.3.5
	 *
	 * @param main
	 * @param node
	 * @param loc
	 * @param methodName
	 * @return
	 */
	private Result handleRealloc(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String methodName) {
		final MemoryModelDeclarations reallocMmDecl = MemoryModelDeclarations.C_REALLOC;

		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 2, methodName, arguments);

		final ICType voidPointerType = CPointer.voidPointer();
		final ExpressionResult ptr = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc,
				arguments[0], voidPointerType);

		final ExpressionResult size = mExprResultTransformer.transformDispatchDecaySwitchImplicitConversion(main, loc,
				arguments[1], mTypeSizeComputer.getSizeT());

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		resultBuilder.addAllExceptLrValue(ptr);
		resultBuilder.addAllExceptLrValue(size);

		final AuxVarInfo auxvarinfo =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, ptr.getLrValue().getCType(), SFO.AUXVAR.REALLOCRES);

		final CallStatement call = StatementFactory.constructCallStatement(loc, false,
				new VariableLHS[] { auxvarinfo.getLhs() }, reallocMmDecl.getName(),
				new Expression[] { ptr.getLrValue().getValue(), size.getLrValue().getValue() });

		resultBuilder.addAuxVarWithDeclaration(auxvarinfo);
		resultBuilder.addStatement(call);
		resultBuilder.setLrValue(new RValue(auxvarinfo.getExp(), CPointer.voidPointer()));

		// add marker for global declaration to memory handler
		mMemoryHandler.requireMemoryStructureFeature(reallocMmDecl);

		// add required information to function handler.
		mProcedureManager.registerProcedure(reallocMmDecl.getName());

		return resultBuilder.build();
	}

	private Result handleMalloc(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String methodName) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, methodName, arguments);

		final ExpressionResult exprRes =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult exprResConverted =
				mExprResultTransformer.performImplicitConversion(exprRes, mTypeSizeComputer.getSizeT(), loc);
		final ExpressionResultBuilder erb = new ExpressionResultBuilder().addAllExceptLrValue(exprResConverted);
		final CPointer resultType = CPointer.voidPointer();
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.MALLOC);
		erb.addAuxVarWithDeclaration(auxvar);

		erb.addStatement(mMemoryHandler.getUltimateMemAllocCall(exprResConverted.getLrValue().getValue(),
				auxvar.getLhs(), loc, MemoryArea.HEAP));
		erb.setLrValue(new RValue(auxvar.getExp(), resultType));

		return erb.build();
	}

	private Result handleRand(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		mHelper.checkArguments(loc, 0, name, node.getArguments());

		final CPrimitive cType = new CPrimitive(CPrimitives.INT);
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.NONDET);
		resultBuilder.addAuxVarWithDeclaration(auxvarinfo);

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

	private Result handleAbs(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name, final CPrimitive resultType) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult argResult =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		builder.addAllExceptLrValue(argResult);
		final Expression expr = argResult.getLrValue().getValue();
		// abs(MIN_INT) does overflow, so add an assertion for overflow checking
		if (mOverflowCheckMode != CheckMode.IGNORE && resultType.isIntegerType()
				&& !mTypeSizes.isUnsigned(resultType)) {
			final Expression minInt = mTypeSizes.constructLiteralForIntegerType(loc, resultType,
					mTypeSizes.getMinValueOfPrimitiveType(resultType));
			final Expression biggerMinInt = mExpressionTranslation.constructBinaryComparisonExpression(loc,
					IASTBinaryExpression.op_greaterThan, expr, resultType, minInt, resultType);
			mExpressionTranslation.addOverflowCheck(loc, biggerMinInt, builder);
		}
		// Construct if x > 0 then x else -x as LrValue for abs(x)
		final Expression positive = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_greaterThan, expr, resultType,
				mTypeSizes.constructLiteralForIntegerType(loc, resultType, BigInteger.ZERO), resultType);
		final Expression negated =
				mExpressionTranslation.constructUnaryExpression(loc, IASTUnaryExpression.op_minus, expr, resultType);
		final Expression iteExpression = ExpressionFactory.constructIfThenElseExpression(loc, positive, expr, negated);
		return builder.setLrValue(new RValue(iteExpression, resultType)).build();
	}

	@Override
	public Collection<TypeModel> getTypeModels() {
		return List.of(new TypeModel("size_t", mTypeSizes.getSizeT()), new TypeModel("ssize_t", mTypeSizes.getSsizeT()),
				new TypeModel("wchar_t", new CPrimitive(CPrimitives.USHORT)));
	}

	@Override
	public Collection<ConstantModel> getConstantModels() {
		return List.of(new ConstantModel("NULL", loc -> new ExpressionResult(
				new RValue(mExpressionTranslation.constructNullPointer(loc), CPointer.voidPointer()))));
	}
}
