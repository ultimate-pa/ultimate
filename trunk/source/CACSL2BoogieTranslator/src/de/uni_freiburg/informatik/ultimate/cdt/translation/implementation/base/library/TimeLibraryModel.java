package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class TimeLibraryModel implements ILibraryModel {
	private final FunctionModelHelper mHelper;
	private final ExpressionTranslation mExpressionTranslation;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	public TimeLibraryModel(final FunctionModelHelper helper, final ExpressionTranslation expressionTranslation,
			final AuxVarInfoBuilder auxVarInfoBuilder) {
		mHelper = helper;
		mExpressionTranslation = expressionTranslation;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();

		/**
		 * 7.27 Date and time <time.h>
		 *
		 * We just overapproximate all functions
		 */
		result.add(new FunctionModel("ctime", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 1, new CPointer(new CPrimitive(CPrimitives.CHAR)))));
		result.add(new FunctionModel("localtime", (main, node, loc, name) -> mHelper.handleByOverapproximation(main,
				node, loc, name, 1, CPointer.voidPointer())));
		result.add(new FunctionModel("mktime", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 1, CPointer.voidPointer())));
		result.add(new FunctionModel("strftime", (main, node, loc, name) -> mHelper.handleByOverapproximation(main,
				node, loc, name, 4, new CPrimitive(CPrimitives.ULONG))));
		// https://en.cppreference.com/w/c/chrono/time
		result.add(new FunctionModel("time", this::handleTime));

		return result;
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return List.of();
	}

	private Result handleTime(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		// TODO: Also write the return value to the pointer, if it is not NULL
		builder.addAllExceptLrValue((ExpressionResult) main.dispatch(arguments[0]));
		final CPrimitive cType = new CPrimitive(CPrimitives.LONG);
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(auxvarinfo);
		final LRValue returnValue = new RValue(auxvarinfo.getExp(), cType);
		builder.setLrValue(returnValue);
		mExpressionTranslation.addAssumeValueInRangeStatements(loc, returnValue.getValue(), returnValue.getCType(),
				builder);
		return builder.build();
	}

	@Override
	public Collection<TypeModel> getTypeModels() {
		return List.of();
	}
}
