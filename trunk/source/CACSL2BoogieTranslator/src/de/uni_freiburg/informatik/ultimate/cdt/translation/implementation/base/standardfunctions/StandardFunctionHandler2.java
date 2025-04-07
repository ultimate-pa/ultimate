package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CExpressionTranslator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationResultReporter;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.DataRaceChecker;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions.StandardFunctionHandler.IFunctionModelHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public abstract class StandardFunctionHandler2 {
	protected final LocationFactory mLocationFactory;
	protected final ExpressionTranslation mExpressionTranslation;
	protected final MemoryHandler mMemoryHandler;
	protected final TypeSizeAndOffsetComputer mTypeSizeComputer;
	protected final ProcedureManager mProcedureManager;
	protected final CTranslationResultReporter mReporter;
	protected final Map<String, IASTNode> mFunctionTable;
	protected final AuxVarInfoBuilder mAuxVarInfoBuilder;
	protected final INameHandler mNameHandler;
	protected final TypeSizes mTypeSizes;
	protected final FlatSymbolTable mSymboltable;
	protected final TranslationSettings mSettings;
	protected final ExpressionResultTransformer mExprResultTransformer;
	protected final ITypeHandler mTypeHandler;
	protected final CExpressionTranslator mCEpressionTranslator;
	protected final DataRaceChecker mDataRaceChecker;
	protected final ILogger mLogger;

	public StandardFunctionHandler2(final ILogger logger, final Map<String, IASTNode> functionTable,
			final AuxVarInfoBuilder auxVarInfoBuilder, final INameHandler nameHandler,
			final ExpressionTranslation expressionTranslation, final MemoryHandler memoryHandler,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final ProcedureManager procedureManager,
			final CTranslationResultReporter reporter, final TypeSizes typeSizes, final FlatSymbolTable symboltable,
			final TranslationSettings settings, final ExpressionResultTransformer expressionResultTransformer,
			final LocationFactory locationFactory, final ITypeHandler typeHandler,
			final CExpressionTranslator cEpressionTranslator, final DataRaceChecker dataRaceChecker) {
		mLogger = logger;
		mExpressionTranslation = expressionTranslation;
		mMemoryHandler = memoryHandler;
		mTypeSizeComputer = typeSizeAndOffsetComputer;
		mProcedureManager = procedureManager;
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
		mCEpressionTranslator = cEpressionTranslator;
		mDataRaceChecker = dataRaceChecker;
	}

	public record FunctionModel(String functionName, IFunctionModelHandler model) {
		// empty
	}

	protected static final void checkArguments(final ILocation loc, final int expectedArgs, final String name,
			final IASTInitializerClause[] arguments) {
		if (arguments.length != expectedArgs) {
			throw new IncorrectSyntaxException(loc, name + " is expected to have " + expectedArgs
					+ " arguments, but was called with " + arguments.length);
		}
	}

	/**
	 * Handle a function call by dispatching all arguments and then calling a function with no arguments that has the
	 * name of the function and is marked with the {@link Overapprox} annotation. Additionally it is assumed that the
	 * result is in range of the given type.
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
	protected final Result handleByOverapproximation(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String methodName, final int numberOfArgs, final ICType resultType) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, numberOfArgs, methodName, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		for (final IASTInitializerClause argument : arguments) {
			builder.addAllExceptLrValue((ExpressionResult) main.dispatch(argument));
		}

		final ExpressionResult overapproxCall = constructOverapproximationForFunctionCall(loc, methodName, resultType);
		builder.addAllExceptLrValue(overapproxCall);
		mExpressionTranslation.addAssumeValueInRangeStatements(loc, overapproxCall.getLrValue().getValue(), resultType,
				builder);
		return builder.setLrValue(overapproxCall.getLrValue()).build();
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
	private ExpressionResult constructOverapproximationForFunctionCall(final ILocation loc, final String functionName,
			final ICType resultType) {
		return buildFunctionCall(loc, resultType).addOverapprox(new Overapprox(functionName, loc)).build();
	}

	private ExpressionResultBuilder buildFunctionCall(final ILocation loc, final ICType resultType) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(auxvar);
		builder.setLrValue(new RValue(auxvar.getExp(), resultType));
		return builder;
	}

	/**
	 * Overapproximate the reachability of unsupported functions by translating them to while(true) assert false; where
	 * the assert is labeled with an overapproximation
	 */
	protected final Result handleUnsupportedFunctionByOverapproximation(final IDispatcher main, final ILocation loc,
			final String name, final ICType returnType) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addStatement(ExpressionTranslation.modelUnsupportedFeature(loc, name));
		if (!returnType.isVoidType()) {
			final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, returnType, AUXVAR.NONDET);
			builder.addAuxVarWithDeclaration(auxVar);
			builder.setLrValue(new RValue(auxVar.getExp(), returnType));
		}
		return builder.build();
	}

	/**
	 * We handle a function call by dispatching all arguments, but we then ignore the call completely.
	 *
	 * Useful for void functions that do nothing.
	 */
	protected static final Result handleVoidFunctionBySkipAndDispatch(final IDispatcher main,
			final IASTFunctionCallExpression node, final ILocation loc, final String methodName,
			final int numberOfArgs) {
		final IASTInitializerClause[] arguments = node.getArguments();
		checkArguments(loc, numberOfArgs, methodName, arguments);
		final List<ExpressionResult> results = new ArrayList<>();
		for (final IASTInitializerClause argument : arguments) {
			results.add((ExpressionResult) main.dispatch(argument));
		}
		return new ExpressionResultBuilder().addAllExceptLrValue(results).build();
	}

	public abstract Collection<FunctionModel> getFunctionModels();

	public abstract Collection<String> getUnsupportedFunctions();
}
