package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CExpressionTranslator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationResultReporter;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.DataRaceChecker;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class StdlibStandardFunctionHandler extends StandardFunctionHandler2 {
	public StdlibStandardFunctionHandler(final ILogger logger, final Map<String, IASTNode> functionTable,
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
		result.add(new FunctionModel("atof", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name,
				1, new CPrimitive(CPrimitives.DOUBLE))));
		result.add(new FunctionModel("atoi", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name,
				1, new CPrimitive(CPrimitives.INT))));
		result.add(new FunctionModel("atol", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name,
				1, new CPrimitive(CPrimitives.LONG))));
		result.add(new FunctionModel("atoll", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 1, new CPrimitive(CPrimitives.LONGLONG))));

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
		result.add(new FunctionModel("qsort", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 4, CPointer.voidPointer())));

		return result;
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return List.of("aligned_alloc", "atexit", "at_quick_exit", "_Exit", "quick_exit", "system", "bsearch");
	}

	private Result handleGetenv(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc) {
		final var builder = new ExpressionResultBuilder();

		// dispatch the argument (unless it's a string literal, then we don't need it)
		assert node.getArguments().length == 1 : "unexpected number of arguments to getenv";
		final var arg = node.getArguments()[0];
		if (!isStringLiteral(arg)) {
			final var argRes = (ExpressionResult) main.dispatch(arg);
			builder.addAllExceptLrValue(argRes);
		}

		final var nondetString = getNondetStringOrNull(loc);
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
		checkArguments(loc, 2, name, arguments);

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
		checkArguments(loc, 1, name, arguments);

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
		checkArguments(loc, 2, methodName, arguments);

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
		mMemoryHandler.requireMemoryModelFeature(reallocMmDecl);

		// add required information to function handler.
		mProcedureManager.registerProcedure(reallocMmDecl.getName());

		return resultBuilder.build();
	}

	private Result handleMalloc(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String methodName) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, 1, methodName, arguments);

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
}
