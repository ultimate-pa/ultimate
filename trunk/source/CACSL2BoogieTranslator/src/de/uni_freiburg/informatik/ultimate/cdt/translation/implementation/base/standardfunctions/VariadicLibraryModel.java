package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.TypesResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class VariadicLibraryModel implements ILibraryModel {
	private final FunctionModelHelper mHelper;
	private final MemoryHandler mMemoryHandler;
	private final ProcedureManager mProcedureManager;
	private final ITypeHandler mTypeHandler;
	private final ExpressionResultTransformer mExprResultTransformer;
	private final ExpressionTranslation mExpressionTranslation;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	public VariadicLibraryModel(final FunctionModelHelper helper, final MemoryHandler memoryHandler,
			final ProcedureManager procedureManager, final ITypeHandler typeHandler,
			final ExpressionResultTransformer exprResultTransformer, final ExpressionTranslation expressionTranslation,
			final AuxVarInfoBuilder auxVarInfoBuilder) {
		mHelper = helper;
		mMemoryHandler = memoryHandler;
		mProcedureManager = procedureManager;
		mTypeHandler = typeHandler;
		mExprResultTransformer = exprResultTransformer;
		mExpressionTranslation = expressionTranslation;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		// 7.16 Variable arguments https://en.cppreference.com/w/c/variadic
		return List.of(new FunctionModel("va_start", this::handleVaStart),
				new FunctionModel("__builtin_va_start", this::handleVaStart),
				new FunctionModel("va_end", this::handleVaEnd),
				new FunctionModel("__builtin_va_end", this::handleVaEnd),
				new FunctionModel("va_copy", this::handleVaCopy),
				new FunctionModel("__builtin_va_copy", this::handleVaCopy));
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return List.of();
	}

	private List<Statement> makeVarargAssignment(final ILocation loc, final LRValue lhs, final Expression rhs) {
		if (lhs instanceof LocalLValue) {
			return List.of(StatementFactory.constructSingleAssignmentStatement(loc, ((LocalLValue) lhs).getLhs(), rhs));
		} else if (lhs instanceof HeapLValue) {
			return mMemoryHandler.getWriteCall(loc, (HeapLValue) lhs, rhs, lhs.getCType(), false);
		} else if (lhs instanceof RValue) {
			final RValue rValue = (RValue) lhs;
			return makeVarargAssignment(loc, new HeapLValue(rValue.getValue(), rValue.getCType(), null), rhs);
		} else {
			throw new UnsupportedOperationException("Unsupported type " + lhs.getClass().getSimpleName());
		}
	}

	private Result handleVaStart(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 2, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult arg0 = (ExpressionResult) main.dispatch(arguments[0]);
		builder.addAllExceptLrValue(arg0);
		// The second argument of va_start has to be the rightmost fixed parameter
		// (according to the C standard section 7.16.1.3.4). Therefore we simply dispatch it here.
		builder.addAllExceptLrValue((ExpressionResult) main.dispatch(arguments[1]));
		final String procedure = mProcedureManager.getCurrentProcedureID();
		final IdentifierExpression rhs = new IdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), SFO.VARARGS,
				new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, procedure));
		return builder.addStatements(makeVarargAssignment(loc, arg0.getLrValue(), rhs)).build();
	}

	private Result handleVaEnd(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);

		final ExpressionResult pRex =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);

		final ExpressionResultBuilder resultBuilder =
				new ExpressionResultBuilder().addAllExceptLrValue(pRex).setLrValue(pRex.getLrValue());

		// Translate va_end(valist) to ULTIMATE.dealloc({ base: valist!base, offset: 0 }) to ensure the memory to be
		// freed
		final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		final Expression pointerWithoutOffset = MemoryHandler.constructPointerFromBaseAndOffset(
				MemoryHandler.getPointerBaseAddress(pRex.getLrValue().getValue(), loc), zero, loc);
		final RValue value = new RValue(pointerWithoutOffset, pRex.getCType());

		/*
		 * Add checks for validity of the to be freed pointer if required.
		 */
		resultBuilder.addStatements(mMemoryHandler.getChecksForFreeCall(loc, value));

		/*
		 * Add a call to our internal deallocation procedure Ultimate.dealloc
		 */
		final CallStatement deallocCall = mMemoryHandler.getDeallocCall(value, loc);
		resultBuilder.addStatement(deallocCall);

		return resultBuilder.build();
	}

	/**
	 * Translate va_copy(dst, src) to a simple overapproximation that simply havocs dst (and annotates it with
	 * "overapproximation")
	 */
	private Result handleVaCopy(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 2, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult dst = (ExpressionResult) main.dispatch(arguments[0]);
		builder.addAllExceptLrValue(dst);
		builder.addAllExceptLrValue((ExpressionResult) main.dispatch(arguments[1]));
		final AuxVarInfo auxVarInfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc,
				new CPointer(new CPrimitive(CPrimitives.CHAR)), AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(auxVarInfo);
		final List<Statement> writes = makeVarargAssignment(loc, dst.getLrValue(), auxVarInfo.getExp());
		writes.forEach(new Overapprox(name, loc)::annotate);
		return builder.addStatements(writes).build();
	}

	@Override
	public Collection<TypeModel> getTypeModels() {
		// TODO: Handle also types defined in stdarg.h here
		return List.of(new TypeModel("__builtin_va_list",
				(node, loc) -> new TypesResult(mTypeHandler.constructPointerType(loc), node.isConst(), false,
						new CPointer(new CPrimitive(CPrimitives.CHAR)))));
	}
}
