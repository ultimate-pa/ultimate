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

import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.AuxFunctionDeclarationBuilder.CDIV_IDENTIFIER;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.AuxFunctionDeclarationBuilder.REM_IDENTIFIER;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.VariableDeclarationBuilder.constructVarDecFromTypeContext;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructBitLengthLiteral;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructExpressionFromValue;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.getBitLengthFromType;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;
import de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.Result;

/**
 * Builders for the Boogie statements of binary operations of LLVM-IR.
 *
 * All methods only work on their parameters and do not access any state of the translation.
 */
public final class BinaryInstructionHandler {

	private BinaryInstructionHandler() {
		// utility class, not meant to be instantiated
	}

	/**
	 * Constructs the local variable and the assignment for an add instruction.
	 *
	 * The sum is taken modulo 2^bitLength.
	 *
	 * @param result
	 *            The result to which the local variable and the assignment are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handleAddInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		constructBinaryAssignment(result, instructionType.addInst().typeValue(), instructionType.addInst().value(),
				Operator.ARITHPLUS, identifier, location);
	}

	/**
	 * Constructs the local variable and the assignment for a sub instruction.
	 *
	 * The difference is taken modulo 2^bitLength.
	 *
	 * @param result
	 *            The result to which the local variable and the assignment are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handleSubInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		constructBinaryAssignment(result, instructionType.subInst().typeValue(), instructionType.subInst().value(),
				Operator.ARITHMINUS, identifier, location);
	}

	/**
	 * Constructs the local variable and the assignment for a mul instruction.
	 *
	 * The product is taken modulo 2^bitLength.
	 *
	 * @param result
	 *            The result to which the local variable and the assignment are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handleMulInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		constructBinaryAssignment(result, instructionType.mulInst().typeValue(), instructionType.mulInst().value(),
				Operator.ARITHMUL, identifier, location);
	}

	/**
	 * Constructs the local variable and the assignment for a signed division (sdiv instruction).
	 *
	 * The division is done by the auxiliary function aux#cdiv with the signed flag. The result is taken modulo
	 * 2^bitLength.
	 *
	 * @param result
	 *            The result to which the local variable and the assignment are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handleSDivInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		final LLVMIRParser.ConcreteTypeContext typeContext =
				instructionType.sDivInst().typeValue().firstClassType().concreteType();
		result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
		final int bitLength = getBitLengthFromType(typeContext);
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final Expression leftExpr = constructExpressionFromValue(instructionType.sDivInst().typeValue().value(),
				typeContext, location, false);
		final Expression rightExpr =
				constructExpressionFromValue(instructionType.sDivInst().value(), typeContext, location, false);
		final Expression maxFromBitLengthExpr = constructBitLengthLiteral(location, bitLength, false);
		final Expression isSignedExpr = new IntegerLiteral(location, "1");

		final FunctionApplication funcApp = new FunctionApplication(location, CDIV_IDENTIFIER,
				new Expression[] { leftExpr, rightExpr, maxFromBitLengthExpr, isSignedExpr });

		final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
		final BinaryExpression signedExpr =
				new BinaryExpression(location, Operator.ARITHMOD, funcApp, bitLengthLiteral);
		final AssignmentStatement assignment =
				new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { signedExpr });
		result.addFuncBlock(assignment);
	}

	/**
	 * Constructs the local variable and the assignment for an unsigned division (udiv instruction).
	 *
	 * The quotient is taken modulo 2^bitLength.
	 *
	 * @param result
	 *            The result to which the local variable and the assignment are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handleUDivInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		constructBinaryAssignment(result, instructionType.uDivInst().typeValue(), instructionType.uDivInst().value(),
				Operator.ARITHDIV, identifier, location);
	}

	/**
	 * Constructs the local variable and the assignment for a signed remainder (srem instruction).
	 *
	 * The remainder is computed by the auxiliary function aux#rem with the signed flag. The result is taken modulo
	 * 2^bitLength.
	 *
	 * @param result
	 *            The result to which the local variable and the assignment are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 * @param unitLocation
	 *            The location of the compilation unit that is attached to the call of aux#rem.
	 */
	public static void handleSRemInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location, final LlvmirLocation unitLocation) {
		final LLVMIRParser.ConcreteTypeContext typeContext =
				instructionType.sRemInst().typeValue().firstClassType().concreteType();
		result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
		final int bitLength = getBitLengthFromType(typeContext);
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final Expression leftExpr = constructExpressionFromValue(instructionType.sRemInst().typeValue().value(),
				typeContext, location, false);
		final Expression rightExpr =
				constructExpressionFromValue(instructionType.sRemInst().value(), typeContext, location, false);
		final Expression maxFromBitLengthExpr = constructBitLengthLiteral(location, bitLength, false);
		final Expression isSignedExpr = new IntegerLiteral(location, "1");

		final FunctionApplication remCall = new FunctionApplication(unitLocation, REM_IDENTIFIER,
				new Expression[] { leftExpr, rightExpr, maxFromBitLengthExpr, isSignedExpr });

		final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
		final BinaryExpression signedExpr =
				new BinaryExpression(location, Operator.ARITHMOD, remCall, bitLengthLiteral);
		final AssignmentStatement assignment =
				new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { signedExpr });
		result.addFuncBlock(assignment);
	}

	/**
	 * Constructs the local variable and the assignment for an unsigned remainder (urem instruction).
	 *
	 * The remainder is taken modulo 2^bitLength.
	 *
	 * @param result
	 *            The result to which the local variable and the assignment are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handleURemInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		constructBinaryAssignment(result, instructionType.uRemInst().typeValue(), instructionType.uRemInst().value(),
				Operator.ARITHMOD, identifier, location);
	}

	/**
	 * Constructs the local variable and the assignment for a binary operation whose result is taken modulo 2^bitLength.
	 *
	 * The type of both operands is the type of the left operand.
	 *
	 * @param result
	 *            The result to which the local variable and the assignment are added.
	 * @param leftTypeValue
	 *            The type and the value of the left operand from the LLVM IR parse tree.
	 * @param rightValue
	 *            The value of the right operand from the LLVM IR parse tree.
	 * @param operator
	 *            The Boogie operator that is applied to the two operands.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	private static void constructBinaryAssignment(final Result result,
			final LLVMIRParser.TypeValueContext leftTypeValue, final LLVMIRParser.ValueContext rightValue,
			final Operator operator, final String identifier, final LlvmirLocation location) {
		final LLVMIRParser.ConcreteTypeContext typeContext = leftTypeValue.firstClassType().concreteType();
		result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
		final int bitLength = getBitLengthFromType(typeContext);
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final Expression leftExpr = constructExpressionFromValue(leftTypeValue.value(), typeContext, location, false);
		final Expression rightExpr = constructExpressionFromValue(rightValue, typeContext, location, false);
		final BinaryExpression binaryExpr = new BinaryExpression(location, operator, leftExpr, rightExpr);
		final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
		final BinaryExpression signedExpr =
				new BinaryExpression(location, Operator.ARITHMOD, binaryExpr, bitLengthLiteral);
		final AssignmentStatement assignment =
				new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { signedExpr });
		result.addFuncBlock(assignment);
	}
}