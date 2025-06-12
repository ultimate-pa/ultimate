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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Model of functions to handle variadic arguments from stdarg.h (C11 7.1, https://en.cppreference.com/w/c/variadic),
 * incl. the GCC builtins for this purpose.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
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
		return List.of(new FunctionModel("va_start", this::handleVaStart),
				new FunctionModel("__builtin_va_start", this::handleVaStart),
				new FunctionModel("va_end", this::handleVaEnd),
				new FunctionModel("__builtin_va_end", this::handleVaEnd),
				new FunctionModel("va_copy", this::handleVaCopy),
				new FunctionModel("__builtin_va_copy", this::handleVaCopy));
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
		final ICType charPointer = new CPointer(new CPrimitive(CPrimitives.CHAR));
		return List.of(new TypeModel("__builtin_va_list", charPointer), new TypeModel("va_list", charPointer));
	}
}
