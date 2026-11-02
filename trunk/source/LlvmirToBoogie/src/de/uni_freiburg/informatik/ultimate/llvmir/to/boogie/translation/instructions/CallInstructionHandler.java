/*
 * Copyright (C) 2025 Peter Ritter
 *
 * This file is part of the ULTIMATE LlvmirToBoogie plug-in.
 * It is used to monitor the parsing of LLVM IR files and to translate them into a Boogie AST.
 *
 * The ULTIMATE LlvmirToBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LlvmirToBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LlvmirToBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LlvmirToBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LlvmirToBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions;

import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.bitLengthPairExists;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.constructBitLengthPairTypeDeclaration;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.constructSpecFromIdentifier;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.constructVarDecFromTypeContext;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.ProcedureBuilder.getProcedureFromDeclarations;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.constructLlvmOperationWithOverflow;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructBitLengthLiteral;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructExpressionFromValue;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructSignedExpression;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.getBitLengthFromType;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.unifyIdentifier;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;
import de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.Result;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Builders for the Boogie statements of call instructions of LLVM-IR.
 *
 * All methods only work on their parameters and do not access any state of the translation.
 */
public final class CallInstructionHandler {

	private static final Set<String> NONDET_FUNCTIONS = Set.of("@__VERIFIER_nondet_int", "@__VERIFIER_nondet_short",
			"@__VERIFIER_nondet_ushort", "@__VERIFIER_nondet_bool", "@__VERIFIER_nondet_ulong",
			"@__VERIFIER_nondet_uint128", "@__VERIFIER_nondet_uint", "@__VERIFIER_nondet_ulonglong",
			"@__VERIFIER_nondet_char", "@__VERIFIER_nondet_uchar");

	private CallInstructionHandler() {
		// utility class, not meant to be instantiated
	}

	/**
	 * Constructs the local variable and the statements for a call instruction whose result is assigned.
	 *
	 * @param result
	 *            The result to which the local variable and the statements are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 * @param declarations
	 *            The declarations of the translation so far.
	 * @throws AssertionError
	 *             if the call instruction has no type or the called procedure is not declared.
	 */
	public static void handleCallInstWithResult(final Result result,
			final LLVMIRParser.ValueInstructionContext instructionType, final String identifier,
			final LlvmirLocation location, final ArrayList<Declaration> declarations) {
		final LLVMIRParser.CallInstContext callInst = instructionType.callInst();
		final LLVMIRParser.TypeContext typeContext = getCallResultType(callInst);
		result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
		final String callIdentifier = callInst.value().constant().getText();
		if (callIdentifier.equals("@printf")) {
			result.addFuncBlock(constructHavocStatement(identifier, location));
		} else if (NONDET_FUNCTIONS.contains(callIdentifier)) {
			addNondetStatements(result, typeContext, identifier, location);
		} else if (callIdentifier.equals("@llvm.abs.i32")) {
			result.addFuncBlock(constructAbsAssignment(callInst.args().arg(0), identifier, location));
		} else if (callIdentifier.startsWith("@llvm.sadd.with.overflow")) {
			addOperationWithOverflow(result, callInst, Operator.ARITHPLUS, true, identifier, location, declarations);
		} else if (callIdentifier.startsWith("@llvm.uadd.with.overflow")) {
			addOperationWithOverflow(result, callInst, Operator.ARITHPLUS, false, identifier, location, declarations);
		} else if (callIdentifier.startsWith("@llvm.ssub.with.overflow")) {
			addOperationWithOverflow(result, callInst, Operator.ARITHMINUS, true, identifier, location, declarations);
		} else if (callIdentifier.startsWith("@llvm.usub.with.overflow")) {
			addOperationWithOverflow(result, callInst, Operator.ARITHMINUS, false, identifier, location, declarations);
		} else if (callIdentifier.startsWith("@llvm.smul.with.overflow")) {
			addOperationWithOverflow(result, callInst, Operator.ARITHMUL, true, identifier, location, declarations);
		} else if (callIdentifier.startsWith("@llvm.umul.with.overflow")) {
			addOperationWithOverflow(result, callInst, Operator.ARITHMUL, false, identifier, location, declarations);
		} else {
			addModifiedGlobalVars(result, callIdentifier, location, declarations);
			final ArrayList<Expression> args = new ArrayList<>();
			for (final LLVMIRParser.ArgContext arg : callInst.args().arg()) {
				args.add(constructExpressionFromValue(arg.value(), typeContext, location, false));
			}
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final CallStatement callStmt = new CallStatement(location, false, new VariableLHS[] { varLhs },
					unifyIdentifier(callIdentifier), args.toArray(Expression[]::new));
			result.addFuncBlock(callStmt);
		}
	}

	/**
	 * Constructs the statements for a call instruction whose result is not assigned.
	 *
	 * @param ctx
	 *            The parse tree context for the call instruction.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 * @param declarations
	 *            The declarations of the translation so far.
	 * @return A Result object containing the CallStatement or AssertStatement.
	 * @throws AssertionError
	 *             if the called procedure is not declared.
	 */
	public static Result handleCallInstWithoutResult(final LLVMIRParser.CallInstContext ctx,
			final LlvmirLocation location, final ArrayList<Declaration> declarations) {
		final Result result = new Result();

		final String callIdentifier = ctx.value().constant().getText();
		if (callIdentifier.equals("@__assert_fail") || callIdentifier.equals("@__VERIFIER_error")) {
			result.addFuncBlock(constructAssertFalse(location));
		} else if (callIdentifier.equals("@printf")) {
			// This call can be ignored as it is not relevant for the Boogie translation
		} else {
			addModifiedGlobalVars(result, callIdentifier, location, declarations);
			final ArrayList<Expression> args = new ArrayList<>();
			for (final LLVMIRParser.ArgContext arg : ctx.args().arg()) {
				args.add(constructExpressionFromValue(arg.value(), arg.concreteType(), location, false));
			}
			final CallStatement callStmt = new CallStatement(location, false, new VariableLHS[] {},
					unifyIdentifier(callIdentifier), args.toArray(Expression[]::new));
			result.addFuncBlock(callStmt);
		}
		return result;
	}

	/**
	 * Retrieves the type of the value that is returned by a call instruction.
	 *
	 * @param callInst
	 *            The parse tree context for the call instruction.
	 * @return The type context of the returned value.
	 * @throws AssertionError
	 *             if the call instruction has no type.
	 */
	private static LLVMIRParser.TypeContext getCallResultType(final LLVMIRParser.CallInstContext callInst) {
		if (callInst.type().type() != null) {
			return callInst.type().type();
		} else if (callInst.type() != null) {
			return callInst.type();
		}
		throw new AssertionError("The support for call instructions without a type is not implemented yet.");
	}

	/**
	 * Constructs a havoc statement for the variable with the given identifier.
	 *
	 * @param identifier
	 *            The identifier of the variable.
	 * @param location
	 *            The location in the source code where the instruction is defined.
	 * @return The havoc statement.
	 */
	private static HavocStatement constructHavocStatement(final String identifier, final LlvmirLocation location) {
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		return new HavocStatement(location, new VariableLHS[] { varLhs });
	}

	/**
	 * Adds the statements for a call of a nondet function of the verifier: The variable is havoced and assumed to be
	 * within the range of its bit length.
	 *
	 * @param result
	 *            The result to which the statements are added.
	 * @param typeContext
	 *            The type of the variable that receives the result.
	 * @param identifier
	 *            The identifier of the variable that receives the result.
	 * @param location
	 *            The location in the source code where the instruction is defined.
	 */
	private static void addNondetStatements(final Result result, final LLVMIRParser.TypeContext typeContext,
			final String identifier, final LlvmirLocation location) {
		result.addFuncBlock(constructHavocStatement(identifier, location));

		final int bitLength = getBitLengthFromType(typeContext);
		final String maxValue = BigInteger.ONE.shiftLeft(bitLength).subtract(BigInteger.ONE).toString();
		result.addFuncBlock(constructBoundAssumption(Operator.COMPLEQ, identifier, maxValue, location));
		result.addFuncBlock(constructBoundAssumption(Operator.COMPGEQ, identifier, "0", location));
	}

	/**
	 * Constructs an assume statement that compares a variable with a constant bound.
	 *
	 * @param operator
	 *            The comparison operator, with the variable as left operand.
	 * @param identifier
	 *            The identifier of the variable.
	 * @param bound
	 *            The integer literal that the variable is compared with.
	 * @param location
	 *            The location in the source code where the instruction is defined.
	 * @return The assume statement.
	 */
	private static AssumeStatement constructBoundAssumption(final Operator operator, final String identifier,
			final String bound, final LlvmirLocation location) {
		final BinaryExpression comparison = new BinaryExpression(location, operator,
				new IdentifierExpression(location, identifier), new IntegerLiteral(location, bound));
		return new AssumeStatement(location, new NamedAttribute[] {}, comparison);
	}

	/**
	 * Constructs the assignment for a call of @llvm.abs.i32: The variable receives the negated argument if it is
	 * negative and the argument otherwise.
	 *
	 * @param arg
	 *            The argument of the call.
	 * @param identifier
	 *            The identifier of the variable that receives the result.
	 * @param location
	 *            The location in the source code where the instruction is defined.
	 * @return The assignment statement.
	 */
	private static AssignmentStatement constructAbsAssignment(final LLVMIRParser.ArgContext arg,
			final String identifier, final LlvmirLocation location) {
		final LLVMIRParser.ConcreteTypeContext argType = arg.concreteType();
		final LLVMIRParser.ValueContext argValue = arg.value();
		final int bitLength = getBitLengthFromType(argType);
		final BinaryExpression isNegative = new BinaryExpression(location, Operator.COMPLT,
				constructOperand(argValue, argType, bitLength, true, location), new IntegerLiteral(location, "0"));
		final BinaryExpression negationExpr = new BinaryExpression(location, Operator.ARITHMINUS,
				new IntegerLiteral(location, "0"), constructOperand(argValue, argType, bitLength, true, location));
		final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
		final BinaryExpression thenExpr =
				new BinaryExpression(location, Operator.ARITHMOD, negationExpr, bitLengthLiteral);
		final Expression elseExpr = constructExpressionFromValue(argValue, argType, location, false);
		final IfThenElseExpression ifThenElseExpr = new IfThenElseExpression(location, isNegative, thenExpr, elseExpr);
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		return new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { ifThenElseExpr });
	}

	/**
	 * Adds the local variable and the assignment for a call of one of the LLVM intrinsics with overflow. The
	 * declaration of the struct type for the bit length of the arguments is added to the declarations if it is not
	 * present yet.
	 *
	 * @param result
	 *            The result to which the local variable and the assignment are added.
	 * @param callInst
	 *            The parse tree context for the call instruction.
	 * @param operator
	 *            The arithmetic operator of the intrinsic.
	 * @param signed
	 *            True if the arguments are interpreted as signed values.
	 * @param identifier
	 *            The identifier of the variable that receives the result.
	 * @param location
	 *            The location in the source code where the instruction is defined.
	 * @param declarations
	 *            The declarations of the translation so far.
	 */
	private static void addOperationWithOverflow(final Result result, final LLVMIRParser.CallInstContext callInst,
			final Operator operator, final boolean signed, final String identifier, final LlvmirLocation location,
			final ArrayList<Declaration> declarations) {
		final LLVMIRParser.ArgContext arg0 = callInst.args().arg(0);
		final LLVMIRParser.ArgContext arg1 = callInst.args().arg(1);
		final LLVMIRParser.ConcreteTypeContext argType = arg0.concreteType();
		final int bitLength = getBitLengthFromType(argType);
		final BinaryExpression expr = new BinaryExpression(location, operator,
				constructOperand(arg0.value(), argType, bitLength, signed, location),
				constructOperand(arg1.value(), argType, bitLength, signed, location));
		if (!bitLengthPairExists(bitLength, declarations)) {
			declarations.add(constructBitLengthPairTypeDeclaration(bitLength, location));
		}
		final Pair<VariableDeclaration, AssignmentStatement> operationWithOverflowPair =
				constructLlvmOperationWithOverflow(expr, bitLength, signed, identifier, location);
		result.addFuncLocalVar(operationWithOverflowPair.getFirst());
		result.addFuncBlock(operationWithOverflowPair.getSecond());
	}

	/**
	 * Constructs the expression of an argument, wrapped into a signed expression if the argument is signed.
	 *
	 * @param value
	 *            The value of the argument.
	 * @param type
	 *            The type of the argument.
	 * @param bitLength
	 *            The bit length of the type.
	 * @param signed
	 *            True if the argument is interpreted as signed value.
	 * @param location
	 *            The location in the source code where the instruction is defined.
	 * @return The expression for the argument.
	 */
	private static Expression constructOperand(final LLVMIRParser.ValueContext value,
			final LLVMIRParser.ConcreteTypeContext type, final int bitLength, final boolean signed,
			final LlvmirLocation location) {
		final Expression operand = constructExpressionFromValue(value, type, location, false);
		return signed ? constructSignedExpression(operand, bitLength, location) : operand;
	}

	/**
	 * Adds the modified global variables of the called procedure to the result.
	 *
	 * @param result
	 *            The result to which the modified global variables are added.
	 * @param callIdentifier
	 *            The identifier of the called procedure.
	 * @param location
	 *            The location in the source code where the instruction is defined.
	 * @param declarations
	 *            The declarations of the translation so far.
	 * @throws AssertionError
	 *             if the called procedure is not declared.
	 */
	private static void addModifiedGlobalVars(final Result result, final String callIdentifier,
			final LlvmirLocation location, final ArrayList<Declaration> declarations) {
		final Procedure proc = getProcedureFromDeclarations(unifyIdentifier(callIdentifier), declarations);
		for (final Specification spec : proc.getSpecification()) {
			if (!(spec instanceof ModifiesSpecification)) {
				continue;
			}
			for (final VariableLHS varLhs : ((ModifiesSpecification) spec).getIdentifiers()) {
				final String varIdentifier = varLhs.getIdentifier();
				result.addFuncModifiedGlobalVar(constructSpecFromIdentifier(varIdentifier, location));
			}
		}
	}

	/**
	 * Constructs an assert false statement that is annotated as assertion check.
	 *
	 * @param location
	 *            The location in the source code where the instruction is defined.
	 * @return The assert statement.
	 */
	private static AssertStatement constructAssertFalse(final LlvmirLocation location) {
		final BooleanLiteral boolLit = new BooleanLiteral(location, false);
		final AssertStatement assertStmt = new AssertStatement(location, new NamedAttribute[] {}, boolLit);
		final Check chk = new Check(Spec.ASSERT);
		chk.annotate(assertStmt);
		return assertStmt;
	}
}