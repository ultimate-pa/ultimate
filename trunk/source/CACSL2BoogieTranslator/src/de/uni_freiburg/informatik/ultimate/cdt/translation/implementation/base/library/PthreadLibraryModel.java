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

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTIdExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.IMemoryPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValueFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Model of functions and types from pthread.h (https://pubs.opengroup.org/onlinepubs/009696899/basedefs/pthread.h.html)
 * to use concurrency in C
 */
public class PthreadLibraryModel implements ILibraryModel {
	private final FunctionModelHelper mHelper;
	private final FlatSymbolTable mSymboltable;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final ExpressionResultTransformer mExprResultTransformer;
	private final ExpressionTranslation mExpressionTranslation;
	private final MemoryHandler mMemoryHandler;
	private final ITypeHandler mTypeHandler;
	private final TypeSizes mTypeSizes;
	private final ProcedureManager mProcedureManager;
	private final ThreadIdManager mThreadIdManager;
	private final IMemoryPointer mMemoryPointer;

	// The constant PTHREAD_BARRIER_SERIAL_THREAD is defined in <pthread.h> and its value shall be distinct from any
	// other value returned by pthread_barrier_wait()
	// (see https://aws.github.io/amazon-freertos/202007.00/html2/POSIX/pthread_8h.html)
	private static final int PTHREAD_BARRIER_SERIAL_THREAD = -2;

	public PthreadLibraryModel(final FunctionModelHelper helper, final FlatSymbolTable symboltable,
			final AuxVarInfoBuilder auxVarInfoBuilder, final ExpressionResultTransformer exprResultTransformer,
			final ExpressionTranslation expressionTranslation, final MemoryHandler memoryHandler,
			final ITypeHandler typeHandler, final TypeSizes typeSizes, final ProcedureManager procedureManager,
			final IMemoryPointer memoryPointer) {
		mHelper = helper;
		mSymboltable = symboltable;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mExprResultTransformer = exprResultTransformer;
		mExpressionTranslation = expressionTranslation;
		mMemoryHandler = memoryHandler;
		mTypeHandler = typeHandler;
		mTypeSizes = typeSizes;
		mProcedureManager = procedureManager;
		mThreadIdManager = new ThreadIdManager(mAuxVarInfoBuilder, mExprResultTransformer, mExpressionTranslation,
				mMemoryHandler, mTypeHandler, mTypeSizes, null /* TODO */, symboltable);
		mMemoryPointer = memoryPointer;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		return List.of(new FunctionModel("pthread_create", this::handlePthread_create),
				new FunctionModel("pthread_join", this::handlePthread_join),
				new FunctionModel("pthread_mutex_init", this::handlePthread_mutex_init),
				new FunctionModel("pthread_barrier_init", this::handlePthread_barrier_init),
				new FunctionModel("pthread_barrier_wait", this::handlePthread_barrier_wait),
				new FunctionModel("pthread_mutex_lock", this::handlePthread_mutex_lock),
				new FunctionModel("pthread_mutex_trylock", this::handlePthread_mutex_trylock),
				new FunctionModel("pthread_mutex_unlock", this::handlePthread_mutex_unlock),
				new FunctionModel("pthread_exit", this::handlePthread_exit),
				new FunctionModel("pthread_detach", this::handlePthread_detach),
				new FunctionModel("pthread_cond_init", this::handlePthread_success),
				new FunctionModel("pthread_cond_wait", this::handlePthread_cond_wait),
				new FunctionModel("pthread_cond_signal", this::handlePthread_success),
				new FunctionModel("pthread_cond_broadcast", this::handlePthread_success),
				new FunctionModel("pthread_cond_destroy", this::handlePthread_success),
				new FunctionModel("pthread_mutex_destroy", this::handlePthread_success),
				new FunctionModel("pthread_rwlock_rdlock", this::handlePthread_rwlock_rdlock),
				new FunctionModel("pthread_rwlock_wrlock", this::handlePthread_rwlock_wrlock),
				new FunctionModel("pthread_rwlock_unlock", this::handlePthread_rwlock_unlock));
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return List.of("pthread_attr_init", "pthread_attr_setdetachstate", "pthread_attr_destroy", "pthread_key_create",
				"pthread_getspecific", "pthread_setspecific", "pthread_rwlock_init");
	}

	private Result handlePthread_create(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 4, name, arguments);

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();

		final ExpressionResult argThreadAttributes =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);
		final ExpressionResult argStartRoutine =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[2]);
		final ExpressionResult startRoutineArguments;
		{
			final ExpressionResult tmp =
					mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[3]);
			startRoutineArguments = mExprResultTransformer.performImplicitConversion(tmp, CPointer.voidPointer(), loc);
		}
		builder.addAllExceptLrValue(argThreadAttributes, argStartRoutine, startRoutineArguments);

		final String methodName = getForkedProcedure(node, arguments[2], argStartRoutine);
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

		final Expression[] threadId = mThreadIdManager.updateForkedThreadId(arguments[0], main, loc, node, builder);
		final ForkStatement fs = new ForkStatement(loc, threadId, methodName, forkArguments);
		mProcedureManager.registerForkStatement(fs);
		builder.addStatement(fs);

		final boolean letPthreadCreateAlwaysReturnZero = false;
		final CPrimitive returnValueCType = new CPrimitive(CPrimitive.CPrimitives.INT);
		final Expression returnValue;
		if (letPthreadCreateAlwaysReturnZero) {
			returnValue = mTypeSizes.constructLiteralForIntegerType(loc, returnValueCType, BigInteger.ZERO);
		} else {
			// auxvar for fork return value (status code)
			final AuxVarInfo auxvarinfo =
					mAuxVarInfoBuilder.constructAuxVarInfo(loc, returnValueCType, SFO.AUXVAR.NONDET);
			builder.addAuxVarWithDeclaration(auxvarinfo);
			returnValue = auxvarinfo.getExp();
		}
		final LRValue val = new RValue(returnValue, returnValueCType);

		builder.setLrValue(val);
		return builder.build();
	}

	private String getForkedProcedure(final IASTFunctionCallExpression node, final IASTInitializerClause argument,
			final ExpressionResult argStartRoutine) {
		// We hope that the function is not given by a function pointer that is stored in a variable but directly by the
		// function name
		final String rawProcName;
		if (argument instanceof CASTIdExpression) {
			final CASTIdExpression castIdExpr = (CASTIdExpression) argument;
			rawProcName = castIdExpr.getName().toString();
		} else if (argument instanceof CASTUnaryExpression) {
			final CASTUnaryExpression castUnaryExpr = (CASTUnaryExpression) argument;
			if (castUnaryExpr.getOperator() != IASTUnaryExpression.op_amper) {
				throw new UnsupportedOperationException(
						"Third argument of pthread_create is: " + argument.getClass().getSimpleName());
			}
			// function foo is probably given as a function pointer of the form & foo
			if (!(castUnaryExpr.getOperand() instanceof CASTIdExpression)) {
				throw new UnsupportedOperationException("Third argument of pthread_create is: "
						+ castUnaryExpr.getOperand().getClass().getSimpleName());
			}
			final CASTIdExpression castIdExpr = (CASTIdExpression) castUnaryExpr.getOperand();
			rawProcName = castIdExpr.getName().toString();
		} else {
			throw new UnsupportedOperationException(
					"Third argument of pthread_create is " + argument.getClass().getSimpleName());
		}

		final String multiParseProcedureName =
				mSymboltable.applyMultiparseRenaming(node.getContainingFilename(), rawProcName);
		if (!mProcedureManager.hasProcedure(multiParseProcedureName)) {
			throw new UnsupportedOperationException("cannot find function " + multiParseProcedureName
					+ " Ultimate does not support pthread_create in combination with function pointers");
		}

		final String id = ((IdentifierExpression) argStartRoutine.getLrValue().getValue()).getIdentifier();
		if (!id.startsWith(SFO.FUNCTION_ADDRESS)) {
			throw new UnsupportedOperationException("unable to decode " + id);
		}
		return id.substring(SFO.FUNCTION_ADDRESS.length());
	}

	// We assume success and return 0 without any additional checks.
	private Result handlePthread_success(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.setLrValue(new RValue(
				mTypeSizes.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT), BigInteger.ZERO),
				new CPrimitive(CPrimitives.INT)));
		return builder.build();
	}

	private Result handlePthread_join(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		// get arguments
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 2, name, arguments);

		// Object that will build our result
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final Expression[] threadId = mThreadIdManager.getJoinedThreadId(arguments[0], main, loc, builder);

		final LRValue argAddressOfResultPointerLr;
		{
			// final ExpressionResult tmp = mExprResultTransformer.dispatchDecaySwitchToRValueFunctionArgument(main,
			// loc, arguments[1]);
			final ExpressionResult tmp = (ExpressionResult) main.dispatch(arguments[1]);
			final ExpressionResult argAddressOfResultPointer =
					mExprResultTransformer.performImplicitConversion(tmp, CPointer.voidPointer(), loc);
			builder.addAllExceptLrValue(argAddressOfResultPointer);
			argAddressOfResultPointerLr = argAddressOfResultPointer.getLrValue();
		}

		final JoinStatement js;
		if (argAddressOfResultPointerLr.isNullPointerConstant(mMemoryPointer)) {
			js = new JoinStatement(loc, threadId, new VariableLHS[0]);
			builder.addStatement(js);
		} else {
			// auxvar for joined procedure's return value
			final ICType cType = CPointer.voidPointer();
			final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.RETURNED);
			builder.addAuxVarWithDeclaration(auxvarinfo);
			js = new JoinStatement(loc, threadId, new VariableLHS[] { auxvarinfo.getLhs() });
			builder.addStatement(js);
			final HeapLValue heapLValue;
			if (argAddressOfResultPointerLr instanceof HeapLValue) {
				heapLValue = (HeapLValue) argAddressOfResultPointerLr;
			} else {
				heapLValue = LRValueFactory.constructHeapLValue(mTypeHandler, argAddressOfResultPointerLr.getValue(),
						cType, false, null);
			}
			final List<Statement> wc = mMemoryHandler.getWriteCall(loc, heapLValue, auxvarinfo.getExp(), cType, false);
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
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);

		final ExpressionResult arg =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult transformedArg =
				mExprResultTransformer.performImplicitConversion(arg, CPointer.voidPointer(), loc);

		final IBoogieType type = mTypeHandler.getBoogiePointerType();
		final String identifier = SFO.RES;
		final DeclarationInformation declarationInformation = new DeclarationInformation(
				StorageClass.IMPLEMENTATION_OUTPARAM, mProcedureManager.getCurrentProcedureID());
		final LeftHandSide[] lhs = { new VariableLHS(loc, type, identifier, declarationInformation) };
		final AssignmentStatement retValAssignment =
				new AssignmentStatement(loc, lhs, new Expression[] { transformedArg.getLrValue().getValue() });
		final ExpressionResultBuilder erb = new ExpressionResultBuilder();
		erb.addAllExceptLrValue(transformedArg);
		erb.addStatement(retValAssignment);
		erb.addStatement(new ReturnStatement(loc));

		return erb.build();
	}

	private Result handlePthread_detach(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		// See https://man7.org/linux/man-pages/man3/pthread_detach.3.html
		// "The pthread_detach() function marks the thread identified by thread as detached. When a detached thread
		// terminates, its resources are automatically released back to the system without the need for another thread
		// to join with the terminated thread."
		// "On success, pthread_detach() returns 0; on error, it returns an error number."
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		// The function just releases resources, without any other effect.
		// Therefore we just dispatch the argument and return a non-deterministic value (indicating success)
		builder.addAllExceptLrValue(
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]));
		final ICType retType = new CPrimitive(CPrimitives.INT);
		final AuxVarInfo retValue = mAuxVarInfoBuilder.constructAuxVarInfo(loc, retType, AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(retValue);
		mExpressionTranslation.addAssumeValueInRangeStatements(loc, retValue.getExp(), retType, builder);
		return builder.setLrValue(new RValue(retValue.getExp(), retType)).build();
	}

	/**
	 * Implements handing for pthread_cond_wait. Since spurious wake-ups are possible (and covered by SVCOMP
	 * benchmarks), we do not actually wait. We merely unlock and lock the mutex.
	 */
	private Result handlePthread_cond_wait(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {

		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 2, name, arguments);

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();

		final ExpressionResult unlock = createPthread_mutex_unlock(main, loc, arguments[1]);
		builder.addAllExceptLrValue(unlock);

		final ExpressionResult lock = createPthread_mutex_lock(main, loc, arguments[1]);
		builder.addAllExceptLrValue(lock);

		builder.setLrValue(new RValue(
				mTypeSizes.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT), BigInteger.ZERO),
				new CPrimitive(CPrimitives.INT)));
		return builder.build();
	}

	/**
	 * We assume that the mutex type is PTHREAD_MUTEX_NORMAL which means that if we lock a mutex that that is already
	 * locked, then the thread blocks.
	 */
	private Result handlePthread_mutex_lock(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		return handleLockCall(main, node, loc, name, mMemoryHandler::constructPthreadMutexLockCall);
	}

	/**
	 * We assume that the mutex type is PTHREAD_MUTEX_NORMAL which means that if we unlock a mutex that has never been
	 * locked, the behavior is undefined. We use a semantics where unlocking a non-locked mutex is a no-op. For the
	 * return value we follow what GCC did in my experiments. It produced code that returned 0 even if we unlocked a
	 * non-locked mutex.
	 */
	private Result handlePthread_mutex_unlock(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		return handleLockCall(main, node, loc, name, mMemoryHandler::constructPthreadMutexUnlockCall);
	}

	private Result handlePthread_mutex_trylock(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		return handleLockCall(main, node, loc, name, mMemoryHandler::constructPthreadMutexTryLockCall);
	}

	private Result handlePthread_rwlock_rdlock(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		return handleLockCall(main, node, loc, name, mMemoryHandler::constructPthreadRwLockReadLockCall);
	}

	private Result handlePthread_rwlock_wrlock(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		return handleLockCall(main, node, loc, name, mMemoryHandler::constructPthreadRwLockWriteLockCall);
	}

	private Result handlePthread_rwlock_unlock(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		return handleLockCall(main, node, loc, name, mMemoryHandler::constructPthreadRwLockUnlockCall);
	}

	private ExpressionResult createPthread_mutex_lock(final IDispatcher main, final ILocation loc,
			final IASTInitializerClause mutex) {
		return handleLockCall(main, loc, "pthread_mutex_lock", mutex, mMemoryHandler::constructPthreadMutexLockCall);
	}

	private ExpressionResult createPthread_mutex_unlock(final IDispatcher main, final ILocation loc,
			final IASTInitializerClause mutex) {
		return handleLockCall(main, loc, "pthread_mutex_unlock", mutex,
				mMemoryHandler::constructPthreadMutexUnlockCall);
	}

	private ExpressionResult handleLockCall(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name, final ILockCallFactory callFactory) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);
		final IASTInitializerClause lock = arguments[0];

		return handleLockCall(main, loc, name, lock, callFactory);
	}

	private ExpressionResult handleLockCall(final IDispatcher main, final ILocation loc, final String name,
			final IASTInitializerClause lock, final ILockCallFactory callFactory) {
		final ExpressionResultBuilder erb = new ExpressionResultBuilder();

		final ExpressionResult arg = mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, lock);
		final Expression index = arg.getLrValue().getValue();
		erb.addAllExceptLrValue(arg);

		// auxvar for procedure's return value
		final ICType cType = new CPrimitive(CPrimitives.INT);
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.RETURNED);
		erb.addAuxVarWithDeclaration(auxvarinfo);

		erb.addStatement(callFactory.apply(loc, index, auxvarinfo.getLhs()));
		erb.setLrValue(new RValue(auxvarinfo.getExp(), new CPrimitive(CPrimitives.INT)));
		return erb.build();
	}

	private interface ILockCallFactory {
		Statement apply(ILocation loc, Expression index, VariableLHS lhs);
	}

	private Result handlePthread_mutex_init(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 2, name, arguments);

		final ExpressionResult arg1 =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult arg2 =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);
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

	private Result handlePthread_barrier_init(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 3, name, arguments);

		final ExpressionResult barrier =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final ExpressionResult attributes =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[1]);
		final ExpressionResult capacity = mExprResultTransformer.performImplicitConversion(
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[2]),
				new CPrimitive(CPrimitives.UINT), loc);
		if (!mMemoryHandler.isNullPointerLiteral(attributes.getLrValue().getValue())) {
			throw new UnsupportedSyntaxException(loc, "Only default attributes are supported for pthread_barrier_init");
		}

		// We model a pthread_barrier using a 3-valued struct:
		// - the number of threads necessary to pass the barrier ("capacity"), initialized with the last parameter
		// - the number of threads that arrived at the barrier, initialized with 0
		// - the number of threads that exited the barrier, initialized with 0
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAllExceptLrValue(barrier, attributes, capacity);
		final Expression zero =
				mTypeSizes.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.UINT), BigInteger.ZERO);
		final Expression barrierInit = ExpressionFactory.constructStructConstructor(loc,
				new String[] { SFO.PTHREAD_BARRIER_CAPACITY, SFO.PTHREAD_BARRIER_ARRIVALS, SFO.PTHREAD_BARRIER_EXITED },
				new Expression[] { capacity.getLrValue().getValue(), zero, zero });
		builder.addStatement(
				mMemoryHandler.constructPthreadBarrierAssignment(loc, barrier.getLrValue().getValue(), barrierInit));
		final CPrimitive returnType = new CPrimitive(CPrimitives.INT);
		return builder.setLrValue(
				new RValue(mTypeSizes.constructLiteralForIntegerType(loc, returnType, BigInteger.ZERO), returnType))
				.build();
	}

	private Result handlePthread_barrier_wait(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 1, name, arguments);

		final ExpressionResult barrier =
				mExprResultTransformer.transformDispatchDecaySwitchRexBoolToInt(main, loc, arguments[0]);
		final Expression index = barrier.getLrValue().getValue();
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAllExceptLrValue(barrier);

		final CPrimitive counterType = new CPrimitive(CPrimitives.UINT);
		final CPrimitive returnType = new CPrimitive(CPrimitives.INT);
		final Expression countAtBarrier =
				mMemoryHandler.constructPthreadBarrierFieldAccess(loc, index, SFO.PTHREAD_BARRIER_CAPACITY);
		final Expression arrivalsAtBarrier =
				mMemoryHandler.constructPthreadBarrierFieldAccess(loc, index, SFO.PTHREAD_BARRIER_ARRIVALS);
		final Expression exitedAtBarrier =
				mMemoryHandler.constructPthreadBarrierFieldAccess(loc, index, SFO.PTHREAD_BARRIER_EXITED);
		final Expression one = mTypeSizes.constructLiteralForIntegerType(loc, counterType, BigInteger.ONE);
		final Expression zero = mTypeSizes.constructLiteralForIntegerType(loc, counterType, BigInteger.ZERO);
		final Expression arrivalsBelowCapacity = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessThan, arrivalsAtBarrier, counterType, countAtBarrier, counterType);
		final Expression nextArrivalCount = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_plus, arrivalsAtBarrier, counterType, one, counterType);

		// Check whether the barrier is already full and otherwise indicate that the thread has arrived
		// atomic { assume arrivals < capacity; arrivals := arrivals + 1; }
		builder.addStatement(StatementFactory.constructAtomicStatement(loc,
				List.of(new AssumeStatement(loc, arrivalsBelowCapacity),
						mMemoryHandler.constructPthreadBarrierFieldAssignment(loc, index, SFO.PTHREAD_BARRIER_ARRIVALS,
								nextArrivalCount))));

		// Wait until all threads have arrived
		// assume arrivals == capacity;
		final Expression allArrived = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_equals, arrivalsAtBarrier, counterType, countAtBarrier, counterType);
		builder.addStatement(new AssumeStatement(loc, allArrived));

		final Expression nextExitedCount = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_plus, exitedAtBarrier, counterType, one, counterType);
		final Expression isLastDeparture = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_equals, nextExitedCount, counterType, countAtBarrier, counterType);
		final Expression nextArrivalState =
				ExpressionFactory.constructIfThenElseExpression(loc, isLastDeparture, zero, arrivalsAtBarrier);
		final Expression nextExitedState =
				ExpressionFactory.constructIfThenElseExpression(loc, isLastDeparture, zero, nextExitedCount);
		final AuxVarInfo returnValue = mAuxVarInfoBuilder.constructAuxVarInfo(loc, returnType, SFO.AUXVAR.RETURNED);
		builder.addAuxVarWithDeclaration(returnValue);

		// Record this thread's exit, the last exit resets the counters for the next round.
		// atomic {
		// newExited := exited + 1;
		// isLast := newExited == capacity;
		// arrivals := if isLast then 0 else arrivals;
		// result := if isLast then PTHREAD_BARRIER_SERIAL_THREAD else 0;
		// exited := if isLast then 0 else newExited;
		// }

		final Expression returnExpression = ExpressionFactory.constructIfThenElseExpression(loc, isLastDeparture,
				mTypeSizes.constructLiteralForIntegerType(loc, returnType,
						BigInteger.valueOf(PTHREAD_BARRIER_SERIAL_THREAD)),
				zero);
		// The exit is assigned last, so the conditions above still observe its old value
		builder.addStatement(StatementFactory.constructAtomicStatement(loc, List.of(
				mMemoryHandler.constructPthreadBarrierFieldAssignment(loc, index, SFO.PTHREAD_BARRIER_ARRIVALS,
						nextArrivalState),
				StatementFactory.constructSingleAssignmentStatement(loc, returnValue.getLhs(), returnExpression),
				mMemoryHandler.constructPthreadBarrierFieldAssignment(loc, index, SFO.PTHREAD_BARRIER_EXITED,
						nextExitedState))));

		return builder.setLrValue(new RValue(returnValue.getExp(), returnType)).build();
	}

	@Override
	public Collection<TypeModel> getTypeModels() {
		// TODO: Handle more types here that are declared in pthread.h
		return List.of(new TypeModel("pthread_t", mTypeHandler.getThreadIdType()),
				new TypeModel("__pthread_list_t", CPointer.voidPointer()),
				// TODO: We may want to use a specific type to simplify the mutex/lock handling
				new TypeModel("pthread_mutex_t", new CPrimitive(CPrimitives.INT)),
				new TypeModel("pthread_barrier_t", new CPrimitive(CPrimitives.INT)),
				new TypeModel("pthread_rwlock_t", new CPrimitive(CPrimitives.INT)),
				new TypeModel("pthread_cond_t", new CPrimitive(CPrimitives.INT)));
	}

	@Override
	public Collection<ConstantModel> getConstantModels() {
		// TODO: Add more constants?
		// TODO: Model initializers properly?
		return List.of(
				new ConstantModel("PTHREAD_MUTEX_INITIALIZER",
						loc -> mHelper.constructIntegerLiteral(loc, BigInteger.ZERO, new CPrimitive(CPrimitives.INT))),
				new ConstantModel("PTHREAD_BARRIER_SERIAL_THREAD",
						loc -> mHelper.constructIntegerLiteral(loc, BigInteger.valueOf(PTHREAD_BARRIER_SERIAL_THREAD),
								new CPrimitive(CPrimitives.INT))),
				new ConstantModel("PTHREAD_RWLOCK_INITIALIZER",
						loc -> mHelper.constructIntegerLiteral(loc, BigInteger.ZERO, new CPrimitive(CPrimitives.INT))),
				new ConstantModel("PTHREAD_COND_INITIALIZER",
						loc -> mHelper.constructIntegerLiteral(loc, BigInteger.ZERO, new CPrimitive(CPrimitives.INT))));
	}
}
