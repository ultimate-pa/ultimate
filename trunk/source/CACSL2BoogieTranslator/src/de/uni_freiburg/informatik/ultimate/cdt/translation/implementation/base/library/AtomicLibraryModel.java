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

public class AtomicLibraryModel implements ILibraryModel {
	/**
	 * See MEMORY_ORDER_SEQ_CST in stdatomic.h
	 */
	private static final int MEMORY_ORDER_SEQ_CST = 5;

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
		// Preprocessing leads to: https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html

		result.add(new FunctionModel("__atomic_load", this::handleAtomicLoad));
		result.add(new FunctionModel("__atomic_store", this::handleAtomicStore));
		result.add(new FunctionModel("__atomic_exchange", this::handleAtomicExchange));
		result.add(new FunctionModel("__atomic_compare_exchange", this::handleAtomicCompareExchange));

		result.add(new FunctionModel("__atomic_load_n", this::handleAtomicLoadN));
		result.add(new FunctionModel("__atomic_store_n", this::handleAtomicStoreN));
		result.add(new FunctionModel("__atomic_exchange_n", this::handleAtomicExchangeN));
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

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return List.of();
	}

	private Result handleAtomicClear(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 2, name, arguments);
		final ExpressionResult pointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult memoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[1]);
		builder.addAllExceptLrValue(pointer, memoryOrder);
		final ExpressionResult write =
				mExprResultTransformer.makePointerAssignment(loc, pointer.getLrValue(), mExpressionTranslation
						.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.BOOL), BigInteger.ZERO));
		return builder.addAllExceptLrValue(applyMemoryOrders(loc, write, memoryOrder.getLrValue().getValue())).build();
	}

	private Result handleAtomicTestAndSet(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 2, name, arguments);
		final ExpressionResult pointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResultBuilder atomicBuilder =
				new ExpressionResultBuilder(mExprResultTransformer.readPointerValue(loc, pointer.getLrValue()));
		final CPrimitive boolType = new CPrimitive(CPrimitives.BOOL);
		final Expression value = mExpressionTranslation.constructLiteralForIntegerType(loc, boolType, BigInteger.ONE);
		atomicBuilder
				.addAllExceptLrValue(mExprResultTransformer.makePointerAssignment(loc, pointer.getLrValue(), value));
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult memoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[1]);
		builder.addAllExceptLrValue(pointer, memoryOrder).addAllIncludingLrValue(
				applyMemoryOrders(loc, atomicBuilder.build(), memoryOrder.getLrValue().getValue()));
		return builder.build();
	}

	private Result handleAtomicLoad(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
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

	private Result handleAtomicStore(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
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

	private Result handleAtomicExchange(final IDispatcher main, final IASTFunctionCallExpression node,
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

	// https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html#index-_005f_005fatomic_005fcompare_005fexchange_005fn
	// https://en.cppreference.com/w/c/atomic/atomic_compare_exchange
	private Result handleAtomicCompareExchange(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 6, name, arguments);

		// In this function, the desired value is passed via a pointer.
		final ExpressionResult desiredResult = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[2]);
		final var desiredRead = mExprResultTransformer.readPointerValue(loc, desiredResult.getLrValue());

		return handleAtomicCompareExchange(main, node, loc, desiredResult, desiredRead);
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

		return handleAtomicCompareExchange(main, node, loc, desiredResult, desiredRead);
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
	private Result handleAtomicCompareExchange(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final ExpressionResult desiredResult, final ExpressionResult desiredRead) {
		final IASTInitializerClause[] arguments = node.getArguments();

		// Evaluate the arguments passed to the function. This happens non-atomically.
		final ExpressionResult pointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResult expectedResult = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[1]);
		final ExpressionResult weakResult = mExprResultTransformer
				.transformSwitchRexIntToBool((ExpressionResult) main.dispatch(arguments[3]), loc, node);
		final ExpressionResult successMemoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[4]);
		final ExpressionResult failureMemoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[5]);
		final var resultBuilder = new ExpressionResultBuilder().addAllExceptLrValue(pointer, expectedResult,
				desiredResult, weakResult, successMemoryOrder, failureMemoryOrder);
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
		final var pointerRead = mExprResultTransformer.readPointerValue(loc, pointer.getLrValue());
		final var expectedRead = mExprResultTransformer.readPointerValue(loc, expectedResult.getLrValue());
		final var pointerWrite = mExprResultTransformer.makePointerAssignment(loc, pointer.getLrValue(),
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
		final var atomic = applyMemoryOrders(loc, atomicBody, successMemoryOrder.getLrValue().getValue(),
				failureMemoryOrder.getLrValue().getValue());

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

	private Result handleAtomicLoadN(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 2, name, arguments);
		final ExpressionResult pointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResult read = mExprResultTransformer.readPointerValue(loc, pointer.getLrValue());
		final ExpressionResult memoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[1]);
		return new ExpressionResultBuilder().addAllExceptLrValue(pointer, memoryOrder)
				.addAllIncludingLrValue(applyMemoryOrders(loc, read, memoryOrder.getLrValue().getValue())).build();
	}

	private Result handleAtomicStoreN(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 3, name, arguments);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ExpressionResult pointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResult valueResult =
				mExprResultTransformer.transformDecaySwitch((ExpressionResult) main.dispatch(arguments[1]), loc, node);
		final ExpressionResult memoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[2]);
		builder.addAllExceptLrValue(pointer, valueResult, memoryOrder);
		// Make sure that only the write, but not the read is atomic
		final ExpressionResult write = mExprResultTransformer.makePointerAssignment(loc, pointer.getLrValue(),
				valueResult.getLrValue().getValue());
		return builder.addAllExceptLrValue(applyMemoryOrders(loc, write, memoryOrder.getLrValue().getValue())).build();
	}

	private Result handleAtomicExchangeN(final IDispatcher main, final IASTFunctionCallExpression node,
			final ILocation loc, final String name) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 3, name, arguments);
		final ExpressionResult pointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResult valueResult =
				mExprResultTransformer.transformDecaySwitch((ExpressionResult) main.dispatch(arguments[1]), loc, node);
		final ExpressionResult memoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[2]);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAllExceptLrValue(pointer, valueResult, memoryOrder);
		final ExpressionResultBuilder atomicBuilder =
				new ExpressionResultBuilder(mExprResultTransformer.readPointerValue(loc, pointer.getLrValue()));
		atomicBuilder.addAllExceptLrValue(mExprResultTransformer.makePointerAssignment(loc, pointer.getLrValue(),
				valueResult.getLrValue().getValue()));
		return builder.addAllIncludingLrValue(
				applyMemoryOrders(loc, atomicBuilder.build(), memoryOrder.getLrValue().getValue())).build();
	}

	private Result handleAtomicFetch(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
			final String name, final int operator) {
		final IASTInitializerClause[] arguments = node.getArguments();
		mHelper.checkArguments(loc, 3, name, arguments);
		final ExpressionResult pointer = mExprResultTransformer.dispatchPointerLValue(main, loc, arguments[0]);
		final ExpressionResult operand =
				mExprResultTransformer.transformDecaySwitch((ExpressionResult) main.dispatch(arguments[1]), loc, node);
		final ExpressionResult memoryOrder =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, arguments[2]);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAllExceptLrValue(pointer, operand, memoryOrder);
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
		final Expression seqCst = mExpressionTranslation.constructLiteralForIntegerType(loc, intType,
				BigInteger.valueOf(MEMORY_ORDER_SEQ_CST));
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
		// TODO: Handle types like atomic_int etc. here
		return List.of();
	}
}
