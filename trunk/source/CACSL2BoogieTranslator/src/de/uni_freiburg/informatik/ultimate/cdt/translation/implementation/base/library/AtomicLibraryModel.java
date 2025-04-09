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
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * This class handles functions and types that are defined in stdatomic.h (C11 7.17,
 * https://en.cppreference.com/w/c/atomic), including the GCC atomic functions that are used after preprocessing
 * (https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html).
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class AtomicLibraryModel implements ILibraryModel {
	private enum MemoryOrder {
		RELAXED("memory_order_relaxed", "__ATOMIC_RELAXED", 0), CONSUME("memory_order_consume", "__ATOMIC_CONSUME", 1),
		ACQUIRE("memory_order_acquire", "__ATOMIC_ACQUIRE", 2), RELEASE("memory_order_release", "__ATOMIC_RELEASE", 3),
		ACQ_REL("memory_order_acq_rel", "__ATOMIC_ACQ_REL", 4), SEQ_CST("memory_order_seq_cst", "__ATOMIC_SEQ_CST", 5);

		private final String mFieldName;
		private final String mGccConstantName;
		private final int mValue;

		MemoryOrder(final String fieldName, final String gccConstantName, final int value) {
			mFieldName = fieldName;
			mGccConstantName = gccConstantName;
			mValue = value;
		}

		public String getFieldName() {
			return mFieldName;
		}

		public String getGccConstantName() {
			return mGccConstantName;
		}

		public BigInteger getValue() {
			return BigInteger.valueOf(mValue);
		}
	}

	private final FunctionModelHelper mHelper;
	private final ExpressionResultTransformer mExprResultTransformer;
	private final ExpressionTranslation mExpressionTranslation;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	public AtomicLibraryModel(final FunctionModelHelper helper, final ExpressionResultTransformer exprResultTransformer,
			final ExpressionTranslation expressionTranslation, final AuxVarInfoBuilder auxVarInfoBuilder) {
		mHelper = helper;
		mExprResultTransformer = exprResultTransformer;
		mExpressionTranslation = expressionTranslation;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();

		// Atomic operations https://en.cppreference.com/w/c/atomic
		result.add(new FunctionModel("atomic_load", this::handleAtomicLoad));
		result.add(new FunctionModel("atomic_store", this::handleAtomicStore));
		result.add(new FunctionModel("atomic_exchange", this::handleAtomicExchange));
		result.add(new FunctionModel("atomic_compare_exchange_strong", this::handleAtomicCompareExchange));
		result.add(new FunctionModel("atomic_compare_exchange_weak", this::handleAtomicCompareExchange));

		result.add(new FunctionModel("atomic_load_explicit", this::handleAtomicLoad));
		result.add(new FunctionModel("atomic_store_explicit", this::handleAtomicStore));
		result.add(new FunctionModel("atomic_exchange_explicit", this::handleAtomicExchange));
		result.add(new FunctionModel("atomic_compare_exchange_strong_explicit", this::handleAtomicCompareExchange));
		result.add(new FunctionModel("atomic_compare_exchange_weak_explicit", this::handleAtomicCompareExchange));

		result.add(new FunctionModel("atomic_fetch_add",
				(main, node, loc, name) -> handleAtomicFetch(main, node, loc, name, IASTBinaryExpression.op_plus)));
		result.add(new FunctionModel("atomic_fetch_sub",
				(main, node, loc, name) -> handleAtomicFetch(main, node, loc, name, IASTBinaryExpression.op_minus)));
		result.add(new FunctionModel("atomic_fetch_and", (main, node, loc, name) -> handleAtomicFetch(main, node, loc,
				name, IASTBinaryExpression.op_binaryAnd)));
		result.add(new FunctionModel("atomic_fetch_or",
				(main, node, loc, name) -> handleAtomicFetch(main, node, loc, name, IASTBinaryExpression.op_binaryOr)));
		result.add(new FunctionModel("atomic_fetch_xor", (main, node, loc, name) -> handleAtomicFetch(main, node, loc,
				name, IASTBinaryExpression.op_binaryXor)));

		result.add(new FunctionModel("atomic_fetch_add_explicit",
				(main, node, loc, name) -> handleAtomicFetch(main, node, loc, name, IASTBinaryExpression.op_plus)));
		result.add(new FunctionModel("atomic_fetch_sub_explicit",
				(main, node, loc, name) -> handleAtomicFetch(main, node, loc, name, IASTBinaryExpression.op_minus)));
		result.add(new FunctionModel("atomic_fetch_and_explicit", (main, node, loc, name) -> handleAtomicFetch(main,
				node, loc, name, IASTBinaryExpression.op_binaryAnd)));
		result.add(new FunctionModel("atomic_fetch_or_explicit",
				(main, node, loc, name) -> handleAtomicFetch(main, node, loc, name, IASTBinaryExpression.op_binaryOr)));
		result.add(new FunctionModel("atomic_fetch_xor_explicit", (main, node, loc, name) -> handleAtomicFetch(main,
				node, loc, name, IASTBinaryExpression.op_binaryXor)));

		result.add(new FunctionModel("atomic_test_and_set", this::handleAtomicTestAndSet));
		result.add(new FunctionModel("atomic_clear", this::handleAtomicClear));

		result.add(new FunctionModel("atomic_test_and_set_explicit", this::handleAtomicTestAndSet));
		result.add(new FunctionModel("atomic_clear_explicit", this::handleAtomicClear));

		// Preprocessing leads to: https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
		result.add(new FunctionModel("__atomic_load", this::handleGccAtomicLoad));
		result.add(new FunctionModel("__atomic_store", this::handleGccAtomicStore));
		result.add(new FunctionModel("__atomic_exchange", this::handleGccAtomicExchange));
		result.add(new FunctionModel("__atomic_compare_exchange", this::handleGccAtomicCompareExchange));

		result.add(new FunctionModel("__atomic_load_n", this::handleAtomicLoad));
		result.add(new FunctionModel("__atomic_store_n", this::handleAtomicStore));
		result.add(new FunctionModel("__atomic_exchange_n", this::handleAtomicExchange));
		result.add(new FunctionModel("__atomic_compare_exchange_n", this::handleAtomicCompareExchangeN));

		result.add(new FunctionModel("__atomic_fetch_add",
				(main, node, loc, name) -> handleAtomicFetch(main, node, loc, name, IASTBinaryExpression.op_plus)));
		result.add(new FunctionModel("__atomic_fetch_sub",
				(main, node, loc, name) -> handleAtomicFetch(main, node, loc, name, IASTBinaryExpression.op_minus)));
		result.add(new FunctionModel("__atomic_fetch_and", (main, node, loc, name) -> handleAtomicFetch(main, node, loc,
				name, IASTBinaryExpression.op_binaryAnd)));
		result.add(new FunctionModel("__atomic_fetch_or",
				(main, node, loc, name) -> handleAtomicFetch(main, node, loc, name, IASTBinaryExpression.op_binaryOr)));
		result.add(new FunctionModel("__atomic_fetch_xor", (main, node, loc, name) -> handleAtomicFetch(main, node, loc,
				name, IASTBinaryExpression.op_binaryXor)));

		result.add(new FunctionModel("__atomic_test_and_set", this::handleAtomicTestAndSet));
		result.add(new FunctionModel("__atomic_clear", this::handleAtomicClear));

		result.add(new FunctionModel("__atomic_thread_fence", (main, node, loc, name) -> mHelper
				.handleUnsupportedFunctionByOverapproximation(main, loc, name, new CPrimitive(CPrimitives.VOID))));
		result.add(new FunctionModel("__atomic_signal_fence", (main, node, loc, name) -> mHelper
				.handleUnsupportedFunctionByOverapproximation(main, loc, name, new CPrimitive(CPrimitives.VOID))));
		result.add(new FunctionModel("__atomic_always_lock_free", (main, node, loc, name) -> mHelper
				.handleByOverapproximation(main, node, loc, name, 2, new CPrimitive(CPrimitives.BOOL))));
		result.add(new FunctionModel("__atomic_is_lock_free", (main, node, loc, name) -> mHelper
				.handleByOverapproximation(main, node, loc, name, 2, new CPrimitive(CPrimitives.BOOL))));

		return result;
	}

	private Result handleAtomicClear(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, hasExplicitMemoryOrder(name) ? 2 : 1, name, arguments);
		final ExpressionResult pointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAllExceptLrValue(pointer);
		final ExpressionResult write =
				mExprResultTransformer.makePointerAssignment(loc, pointer.getLrValue(), mExpressionTranslation
						.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.BOOL), BigInteger.ZERO));
		if (!hasExplicitMemoryOrder(name)) {
			return builder.addAllExceptLrValue(applyMemoryOrders(loc, write)).build();
		}
		final ExpressionResult memoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[1]);
		builder.addAllExceptLrValue(memoryOrder);
		return builder.addAllExceptLrValue(applyMemoryOrders(loc, write, memoryOrder.getLrValue().getValue())).build();
	}

	private Result handleAtomicTestAndSet(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, hasExplicitMemoryOrder(name) ? 2 : 1, name, arguments);
		final ExpressionResult pointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResultBuilder atomicBuilder =
				new ExpressionResultBuilder(mExprResultTransformer.readPointerValue(loc, pointer.getLrValue()));
		final CPrimitive boolType = new CPrimitive(CPrimitives.BOOL);
		final Expression value = mExpressionTranslation.constructLiteralForIntegerType(loc, boolType, BigInteger.ONE);
		atomicBuilder
				.addAllExceptLrValue(mExprResultTransformer.makePointerAssignment(loc, pointer.getLrValue(), value));
		final ExpressionResultBuilder builder = new ExpressionResultBuilder().addAllExceptLrValue(pointer);
		if (hasExplicitMemoryOrder(name)) {
			final ExpressionResult memoryOrder =
					mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[1]);
			builder.addAllExceptLrValue(memoryOrder).addAllIncludingLrValue(
					applyMemoryOrders(loc, atomicBuilder.build(), memoryOrder.getLrValue().getValue()));
		} else {
			builder.addAllIncludingLrValue(applyMemoryOrders(loc, atomicBuilder.build()));
		}
		return builder.build();
	}

	private Result handleGccAtomicLoad(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 3, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult pointer1 = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResult pointer2 = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[1]);
		final ExpressionResult memoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[2]);
		builder.addAllExceptLrValue(pointer1, pointer2, memoryOrder);
		// Make sure that only the read, but not the write is atomic
		final ExpressionResult read = mExprResultTransformer.readPointerValue(loc, pointer1.getLrValue());
		final ExpressionResult write =
				mExprResultTransformer.makePointerAssignment(loc, pointer2.getLrValue(), read.getLrValue().getValue());
		return builder.addAllIncludingLrValue(applyMemoryOrders(loc, read, memoryOrder.getLrValue().getValue()))
				.addAllExceptLrValue(write).build();
	}

	private Result handleGccAtomicStore(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 3, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult pointer1 = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResult pointer2 = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[1]);
		final ExpressionResult memoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[2]);
		builder.addAllExceptLrValue(pointer1, pointer2, memoryOrder);
		final ExpressionResult read = mExprResultTransformer.readPointerValue(loc, pointer2.getLrValue());
		builder.addAllExceptLrValue(read);
		// Make sure that only the write, but not the read is atomic
		builder.addAllExceptLrValue(applyMemoryOrders(loc,
				mExprResultTransformer.makePointerAssignment(loc, pointer1.getLrValue(), read.getLrValue().getValue()),
				memoryOrder.getLrValue().getValue()));
		return builder.build();
	}

	private Result handleGccAtomicExchange(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 4, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult pointer1 = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResult pointer2 = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[1]);
		final ExpressionResult pointer3 = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[2]);
		final ExpressionResult memoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[3]);
		builder.addAllExceptLrValue(pointer1, pointer2, pointer3, memoryOrder);
		final ExpressionResult read0 = mExprResultTransformer.readPointerValue(loc, pointer1.getLrValue());
		final ExpressionResultBuilder atomicBuilder = new ExpressionResultBuilder();
		final ExpressionResult read1 = mExprResultTransformer.readPointerValue(loc, pointer2.getLrValue());
		// All reads and writes are atomic
		atomicBuilder.addAllExceptLrValue(read0,
				mExprResultTransformer.makePointerAssignment(loc, pointer3.getLrValue(), read0.getLrValue().getValue()),
				read1, mExprResultTransformer.makePointerAssignment(loc, pointer1.getLrValue(),
						read1.getLrValue().getValue()));
		builder.addAllExceptLrValue(applyMemoryOrders(loc, atomicBuilder.build(), memoryOrder.getLrValue().getValue()));
		return builder.build();
	}

	private Result handleAtomicCompareExchange(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, hasExplicitMemoryOrder(name) ? 5 : 3, name, arguments);

		// In this function, the desired value is passed directly. We create a small dummy ExpressionResult for the
		// helper function and store only the desired LRValue.
		final ExpressionResult desiredResult =
				mExprResultTransformer.transformDecaySwitch((ExpressionResult) main.dispatch(arguments[2]), loc, node);
		final var desiredRead = new ExpressionResult(desiredResult.getLrValue());

		final ExpressionResult weakResult =
				new ExpressionResult(new RValue(ExpressionFactory.createBooleanLiteral(loc, name.contains("weak")),
						new CPrimitive(CPrimitives.BOOL)));

		if (hasExplicitMemoryOrder(name)) {
			final ExpressionResult successMemoryOrder =
					mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[3]);
			final ExpressionResult failureMemoryOrder =
					mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[4]);
			return handleAtomicCompareExchange(main, loc, arguments[0], arguments[1], desiredResult, desiredRead,
					weakResult, successMemoryOrder, failureMemoryOrder);
		}

		return handleAtomicCompareExchange(main, loc, arguments[0], arguments[1], desiredResult, desiredRead,
				weakResult);
	}

	// https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html#index-_005f_005fatomic_005fcompare_005fexchange_005fn
	// https://en.cppreference.com/w/c/atomic/atomic_compare_exchange
	private Result handleGccAtomicCompareExchange(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 6, name, arguments);

		// In this function, the desired value is passed via a pointer.
		final ExpressionResult desiredResult = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[2]);
		final var desiredRead = mExprResultTransformer.readPointerValue(loc, desiredResult.getLrValue());

		final ExpressionResult weakResult = mExprResultTransformer
				.transformSwitchRexIntToBool((ExpressionResult) main.dispatch(arguments[3]), loc, node);
		final ExpressionResult successMemoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[4]);
		final ExpressionResult failureMemoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[5]);

		return handleAtomicCompareExchange(main, loc, arguments[0], arguments[1], desiredResult, desiredRead,
				weakResult, successMemoryOrder, failureMemoryOrder);
	}

	// https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html#index-_005f_005fatomic_005fcompare_005fexchange_005fn
	// https://en.cppreference.com/w/c/atomic/atomic_compare_exchange
	private Result handleAtomicCompareExchangeN(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 6, name, arguments);

		// In this function, the desired value is passed directly. We create a small dummy ExpressionResult for the
		// helper function and store only the desired LRValue.
		final ExpressionResult desiredResult =
				mExprResultTransformer.transformDecaySwitch((ExpressionResult) main.dispatch(arguments[2]), loc, node);
		final var desiredRead = new ExpressionResult(desiredResult.getLrValue());

		final ExpressionResult weakResult = mExprResultTransformer
				.transformSwitchRexIntToBool((ExpressionResult) main.dispatch(arguments[3]), loc, node);
		final ExpressionResult successMemoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[4]);
		final ExpressionResult failureMemoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[5]);

		return handleAtomicCompareExchange(main, loc, arguments[0], arguments[1], desiredResult, desiredRead,
				weakResult, successMemoryOrder, failureMemoryOrder);
	}

	// https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html#index-_005f_005fatomic_005fcompare_005fexchange_005fn
	// https://en.cppreference.com/w/c/atomic/atomic_compare_exchange
	//
	// The implementation below generates Boogie code that roughly follows the schema below, where success and ptr_val
	// are auxiliary variables. However, if the memoryOrder argument is not sequential consistency, we instead
	// overapproximate the method with "assert false".
	//
	// @formatter:off
	// (evaluate arguments)
	// havoc success
	// if (!weak || success) {
	//   atomic {
	//     ptr_val := read(ptr)
	//     success := ptr_val == read(expected)
	//     if (success) {
	//       write(read(desired), ptr)
	//     } else {
	//       write(ptr_val, expected)
	//     }
	//   }
	// }
	// return success
	// @formatter:on
	private Result handleAtomicCompareExchange(final IDispatcher main, final ILocation loc,
			final IASTInitializerClause pointer, final IASTInitializerClause expected,
			final ExpressionResult desiredResult, final ExpressionResult desiredRead, final ExpressionResult weakResult,
			final ExpressionResult... memoryOrders) {
		// Evaluate the arguments passed to the function. This happens non-atomically.
		final ExpressionResult pointerResult = mExprResultTransformer.dispatchPointerLValue(main, loc, pointer);
		final ExpressionResult expectedResult = mExprResultTransformer.dispatchPointerLValue(main, loc, expected);
		final var resultBuilder = new ExpressionResultBuilder()
				.addAllExceptLrValue(pointerResult, expectedResult, desiredResult, weakResult)
				.addAllExceptLrValue(memoryOrders);
		final boolean mayFailSpuriously = !ExpressionFactory.isFalseLiteral(weakResult.getLrValue().getValue());

		// Introduce an auxvar indicating whether the function is successful, i.e., the exchange was performed.
		// We immediately havoc the auxvar.
		final var boolType = new CPrimitive(CPrimitives.BOOL);
		final var success = mAuxVarInfoBuilder.constructAuxVarInfo(loc, boolType, AUXVAR.RETURNED);
		final var successBoolean = mExpressionTranslation.toBool(loc, success.getExp(), boolType);
		resultBuilder.addAuxVarWithDeclaration(success);
		if (mayFailSpuriously) {
			resultBuilder.addStatement(new HavocStatement(loc, new VariableLHS[] { success.getLhs() }));
		}

		// Construct the code that actually executes the compare-and-exchange.
		final var pointerRead = mExprResultTransformer.readPointerValue(loc, pointerResult.getLrValue());
		final var expectedRead = mExprResultTransformer.readPointerValue(loc, expectedResult.getLrValue());
		final var pointerWrite = mExprResultTransformer.makePointerAssignment(loc, pointerResult.getLrValue(),
				desiredRead.getLrValue().getValue());
		final var expectedWrite = mExprResultTransformer.makePointerAssignment(loc, expectedResult.getLrValue(),
				pointerRead.getLrValue().getValue());
		final var atomicBody = new ExpressionResultBuilder().addAllExceptLrValue(pointerRead, expectedRead)
				.addAllExceptLrValueAndStatements(desiredRead).addAllExceptLrValueAndStatements(pointerWrite)
				.addAllExceptLrValueAndStatements(expectedWrite)
				// success := read(ptr) == read(expected)
				.addStatement(StatementFactory.constructSingleAssignmentStatement(loc, success.getLhs(),
						mExpressionTranslation.boolToInt(loc,
								mExpressionTranslation.constructBinaryEqualityExpression(loc,
										IASTBinaryExpression.op_equals, pointerRead.getLrValue().getValue(),
										pointerRead.getLrValue().getCType(), expectedRead.getLrValue().getValue(),
										expectedRead.getCType()),
								boolType.getType())))
				// if (success) { write(read(desired), ptr) } else { write(ptr_val, expected) }
				.addStatement(StatementFactory.constructIfStatement(loc, successBoolean,
						DataStructureUtils.concat(desiredRead.getStatements(), pointerWrite.getStatements()),
						expectedWrite.getStatements()))
				.build();

		// Wrap the compare-exchange in an atomic block, and check if the memory order arguments are supported.
		final var atomic = applyMemoryOrders(loc, atomicBody,
				Arrays.stream(memoryOrders).map(x -> x.getLrValue().getValue()).toArray(Expression[]::new));

		// Wrap atomic compare-exchange block in "if (success || !weak) { ... }" to model spurious failures.
		if (mayFailSpuriously) {
			resultBuilder.addAllExceptLrValueAndStatements(atomic)
					.addStatement(StatementFactory.constructIfStatement(loc,
							ExpressionFactory.or(loc, successBoolean,
									ExpressionFactory.not(loc, weakResult.getLrValue().getValue())),
							atomic.getStatements()));
		} else {
			resultBuilder.addAllExceptLrValue(atomic);
		}

		return resultBuilder.setLrValue(new RValue(success.getExp(), boolType)).build();
	}

	private static boolean hasExplicitMemoryOrder(final String functionName) {
		return functionName.startsWith("__") || functionName.endsWith("explicit");
	}

	private Result handleAtomicLoad(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, hasExplicitMemoryOrder(name) ? 2 : 1, name, arguments);
		final ExpressionResult pointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResult read = mExprResultTransformer.readPointerValue(loc, pointer.getLrValue());
		if (!hasExplicitMemoryOrder(name)) {
			return new ExpressionResultBuilder().addAllExceptLrValue(pointer)
					.addAllIncludingLrValue(applyMemoryOrders(loc, read)).build();
		}
		final ExpressionResult memoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[1]);
		return new ExpressionResultBuilder().addAllExceptLrValue(pointer, memoryOrder)
				.addAllIncludingLrValue(applyMemoryOrders(loc, read, memoryOrder.getLrValue().getValue())).build();
	}

	private Result handleAtomicStore(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, hasExplicitMemoryOrder(name) ? 3 : 2, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult pointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResult valueResult =
				mExprResultTransformer.transformDecaySwitch((ExpressionResult) main.dispatch(arguments[1]), loc, node);
		// Make sure that only the write, but not the read is atomic
		final ExpressionResult write = mExprResultTransformer.makePointerAssignment(loc, pointer.getLrValue(),
				valueResult.getLrValue().getValue());
		builder.addAllExceptLrValue(pointer, valueResult);
		if (!hasExplicitMemoryOrder(name)) {
			return builder.addAllExceptLrValue(applyMemoryOrders(loc, write)).build();
		}
		final ExpressionResult memoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[2]);
		builder.addAllExceptLrValue(memoryOrder);
		return builder.addAllExceptLrValue(applyMemoryOrders(loc, write, memoryOrder.getLrValue().getValue())).build();
	}

	private Result handleAtomicExchange(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, hasExplicitMemoryOrder(name) ? 3 : 2, name, arguments);
		final ExpressionResult pointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResult valueResult =
				mExprResultTransformer.transformDecaySwitch((ExpressionResult) main.dispatch(arguments[1]), loc, node);

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAllExceptLrValue(pointer, valueResult);
		final ExpressionResultBuilder atomicBuilder =
				new ExpressionResultBuilder(mExprResultTransformer.readPointerValue(loc, pointer.getLrValue()));
		atomicBuilder.addAllExceptLrValue(mExprResultTransformer.makePointerAssignment(loc, pointer.getLrValue(),
				valueResult.getLrValue().getValue()));
		if (!hasExplicitMemoryOrder(name)) {
			return builder.addAllIncludingLrValue(applyMemoryOrders(loc, atomicBuilder.build())).build();
		}
		final ExpressionResult memoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[2]);
		builder.addAllExceptLrValue(memoryOrder);
		return builder.addAllIncludingLrValue(
				applyMemoryOrders(loc, atomicBuilder.build(), memoryOrder.getLrValue().getValue())).build();
	}

	private Result handleAtomicFetch(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name, final int operator) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, hasExplicitMemoryOrder(name) ? 3 : 2, name, arguments);
		final ExpressionResult pointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResult operand =
				mExprResultTransformer.transformDecaySwitch((ExpressionResult) main.dispatch(arguments[1]), loc, node);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAllExceptLrValue(pointer, operand);
		final ExpressionResult read = mExprResultTransformer.readPointerValue(loc, pointer.getLrValue());
		final ExpressionResultBuilder atomicBuilder = new ExpressionResultBuilder(read);
		final Expression newValue;
		final CPrimitive readType = (CPrimitive) read.getCType().getUnderlyingType();
		final CPrimitive operandType = (CPrimitive) operand.getCType().getUnderlyingType();
		if (operator == IASTBinaryExpression.op_plus || operator == IASTBinaryExpression.op_minus) {
			newValue = mExpressionTranslation.constructArithmeticExpression(loc, operator, read.getLrValue().getValue(),
					readType, operand.getLrValue().getValue(), operandType);
		} else {
			final ExpressionResult bitwiseResult =
					mExpressionTranslation.handleBinaryBitwiseExpression(loc, operator, read.getLrValue().getValue(),
							readType, operand.getLrValue().getValue(), operandType, mAuxVarInfoBuilder);
			atomicBuilder.addAllExceptLrValue(bitwiseResult);
			newValue = bitwiseResult.getLrValue().getValue();
		}
		atomicBuilder
				.addAllExceptLrValue(mExprResultTransformer.makePointerAssignment(loc, pointer.getLrValue(), newValue));
		// Make sure that only the write, but not the read is atomic
		if (!hasExplicitMemoryOrder(name)) {
			return builder.addAllIncludingLrValue(applyMemoryOrders(loc, atomicBuilder.build())).build();
		}
		final ExpressionResult memoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[2]);
		builder.addAllExceptLrValue(memoryOrder);
		return builder.addAllIncludingLrValue(
				applyMemoryOrders(loc, atomicBuilder.build(), memoryOrder.getLrValue().getValue())).build();
	}

	/**
	 * Apply the given {@code memoryOrders} to the {@code body} for stdatomic-library. If every given memory order is
	 * equal to {@code MEMORY_ORDER_SEQ_CST}, we just make all statements atomic. For all other cases we just
	 * overapproximate (using an {@code assert false}), since we only support sequential consistency.
	 *
	 * @param loc
	 *            The C location
	 * @param body
	 *            The body that should be atomic based on the memory order
	 * @param memoryOrders
	 *            The memory orders to apply
	 * @return An ExpressionResult representing the translation respecting the memory order
	 */
	private ExpressionResult applyMemoryOrders(final ILocation loc, final ExpressionResult body,
			final Expression... memoryOrders) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder(body);
		builder.resetStatements(List.of());

		final Statement atomic = StatementFactory.constructAtomicStatement(loc, body.getStatements());

		// create condition checking whether all memory orders are supported
		final CPrimitive intType = new CPrimitive(CPrimitives.INT);
		final Expression seqCst =
				mExpressionTranslation.constructLiteralForIntegerType(loc, intType, MemoryOrder.SEQ_CST.getValue());
		final var conjuncts = Arrays.stream(memoryOrders)
				.map(memoryOrder -> mExpressionTranslation.constructBinaryEqualityExpression(loc,
						IASTBinaryExpression.op_equals, memoryOrder, intType, seqCst, intType))
				.collect(Collectors.toList());
		final Expression atomicCond = ExpressionFactory.and(loc, conjuncts);

		// overapproximated assert used in case some memory order is unsupported
		final Statement overapproxAssert = ExpressionTranslation.modelUnsupportedFeature(loc,
				"memory order (only sequential consistency is supported)");

		// Try to avoid unnecessary IfStatements
		final Statement statement;
		if (atomicCond instanceof BooleanLiteral) {
			statement = ((BooleanLiteral) atomicCond).getValue() ? atomic : overapproxAssert;
		} else {
			statement =
					new IfStatement(loc, atomicCond, new Statement[] { atomic }, new Statement[] { overapproxAssert });
		}
		return builder.addStatement(statement).build();
	}

	@Override
	public Collection<TypeModel> getTypeModels() {
		return List.of(new TypeModel("atomic_bool", CPrimitive.constructAtomicType(CPrimitives.BOOL)),
				new TypeModel("atomic_char", CPrimitive.constructAtomicType(CPrimitives.CHAR)),
				new TypeModel("atomic_schar", CPrimitive.constructAtomicType(CPrimitives.SCHAR)),
				new TypeModel("atomic_uchar", CPrimitive.constructAtomicType(CPrimitives.UCHAR)),
				new TypeModel("atomic_short", CPrimitive.constructAtomicType(CPrimitives.SHORT)),
				new TypeModel("atomic_ushort", CPrimitive.constructAtomicType(CPrimitives.USHORT)),
				new TypeModel("atomic_int", CPrimitive.constructAtomicType(CPrimitives.INT)),
				new TypeModel("atomic_uint", CPrimitive.constructAtomicType(CPrimitives.UINT)),
				new TypeModel("atomic_long", CPrimitive.constructAtomicType(CPrimitives.LONG)),
				new TypeModel("atomic_ulong", CPrimitive.constructAtomicType(CPrimitives.ULONG)),
				new TypeModel("atomic_llong", CPrimitive.constructAtomicType(CPrimitives.LONGLONG)),
				new TypeModel("atomic_ullong", CPrimitive.constructAtomicType(CPrimitives.ULONGLONG)),
				new TypeModel("memory_order", new CEnum("memory_order",
						Arrays.stream(MemoryOrder.values()).map(MemoryOrder::getFieldName).toArray(String[]::new))));
	}

	@Override
	public Collection<ConstantModel> getConstantModels() {
		final List<ConstantModel> result = new ArrayList<>();
		for (final MemoryOrder memOrder : MemoryOrder.values()) {
			final IConstantModelHandler model =
					loc -> mHelper.constructIntegerLiteral(loc, memOrder.getValue(), new CPrimitive(CPrimitives.INT));
			result.add(new ConstantModel(memOrder.getFieldName(), model));
			result.add(new ConstantModel(memOrder.getGccConstantName(), model));
		}
		return result;
	}
}
