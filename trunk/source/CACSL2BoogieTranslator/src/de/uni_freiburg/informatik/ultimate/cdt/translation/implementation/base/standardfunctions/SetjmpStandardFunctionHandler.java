package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class SetjmpStandardFunctionHandler extends StandardFunctionHandler2 {
	public SetjmpStandardFunctionHandler(final ILogger logger, final Map<String, IASTNode> functionTable,
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

		// longjmp https://en.cppreference.com/w/c/program/longjmp
		// We cannot handle restoring the environment, so we just check if the function is reachable and create an
		// overraproximation for that case
		result.add(new FunctionModel("longjmp",
				(main, node, loc, name) -> handleUnsupportedFunctionByOverapproximation(main, loc, name,
						new CPrimitive(CPrimitives.VOID))));

		// setjmp https://en.cppreference.com/w/c/program/setjmp
		result.add(new FunctionModel("_setjmp", this::handleSetjmp));
		result.add(new FunctionModel("setjmp", this::handleSetjmp));

		return result;
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return List.of();
	}

	// For now we do not handle setjmp properly. We crash on longjmp, so it is sufficient to always return 0 for setjmp.
	private Result handleSetjmp(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final CPrimitive returnType = new CPrimitive(CPrimitives.INT);
		return new ExpressionResult(new RValue(
				mExpressionTranslation.constructLiteralForIntegerType(loc, returnType, BigInteger.ZERO), returnType));
	}
}
