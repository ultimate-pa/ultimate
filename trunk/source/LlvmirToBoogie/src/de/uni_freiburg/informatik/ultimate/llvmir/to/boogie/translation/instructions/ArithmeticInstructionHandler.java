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

import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.AuxFunctionDeclerationBuilder.CDIV_IDENTIFIER;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.AuxFunctionDeclerationBuilder.REM_IDENTIFIER;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.VariableDeclarationBuilder.constructVarDecFromString;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.VariableDeclarationBuilder.constructVarDecFromTypeContext;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructBitLengthLiteral;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructExpressionFromValue;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructSignedExpression;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.getBitLengthFromType;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.getCompOperatorFromOperatorValue;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;
import de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.Result;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Builders for the Boogie statements of arithmetic and logic instructions of LLVM-IR.
 *
 * All methods only work on their parameters and do not access any state of the translation.
 */
public final class ArithmeticInstructionHandler {

	private ArithmeticInstructionHandler() {
		// utility class, not meant to be instantiated
	}

	/**
	 * Constructs a havoc statement for arithmetic or logic instructions.
	 *
	 * This method generates a havoc statement for arithmetic or logic instructions based on the type of the
	 * instruction. It constructs a local variable with either "bool" or "int" type and adds a havoc statement to the
	 * result.
	 *
	 * @param result
	 *            The result to which the havoc statement will be added.
	 * @param typeValue
	 *            The type value context from the LLVM IR parse tree.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 * @param identifier
	 *            The identifier for the local variable to be constructed.
	 */
	public static void constructHavocStatementFromTypeValue(final Result result,
			final LLVMIRParser.TypeValueContext typeValue, final LlvmirLocation location, final String identifier,
			final String reason) {
		final LLVMIRParser.ConcreteTypeContext tpyeContext = typeValue.firstClassType().concreteType();
		result.addFuncLocalVar(constructVarDecFromTypeContext(tpyeContext, identifier, location));
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final HavocStatement havocStmt = new HavocStatement(location, new VariableLHS[] { varLhs });
		final Overapprox overapprox = new Overapprox(reason, location);
		overapprox.annotate(havocStmt);
		result.addFuncBlock(havocStmt);
	}

	/**
	 * Constructs a variable declaration and an assignment statement for an LLVM operation with overflow handling.
	 *
	 * This method creates a VariableDeclaration for a struct type that holds the result of the operation and an
	 * overflow flag. It also constructs an AssignmentStatement that assigns the result of the operation and the
	 * overflow status to the struct fields.
	 *
	 * @param operation
	 *            The expression representing the LLVM operation.
	 * @param bitLength
	 *            The bit length of the integer type involved in the operation.
	 * @param isSigned
	 *            Indicates whether the integer type is signed or unsigned.
	 * @param Identifier
	 *            The identifier for the variable to be declared and assigned.
	 * @param location
	 *            The location in the source code where this operation occurs.
	 * @return A Pair containing the VariableDeclaration and AssignmentStatement.
	 */
	public static Pair<VariableDeclaration, AssignmentStatement> constructLlvmOperationWithOverflow(
			final Expression operation, final int bitLength, final boolean isSigned, final String Identifier,
			final LlvmirLocation location) {
		final NamedType namedType = new NamedType(location, "i" + bitLength + "Pair", new ASTType[] {});
		final VarList varList = new VarList(location, new String[] { Identifier }, namedType);
		final VariableDeclaration varDec =
				new VariableDeclaration(location, new Attribute[] {}, new VarList[] { varList });

		final String[] fieldIdentifiers = { "e0", "e1" };
		final Expression[] fieldValues = {};
		final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
		final BinaryExpression binaryExpr1 =
				new BinaryExpression(location, Operator.ARITHMOD, operation, bitLengthLiteral);
		fieldValues[0] = binaryExpr1;

		final IntegerLiteral signedBitLengthLiteral = constructBitLengthLiteral(location, bitLength, isSigned);
		final BinaryExpression binaryExpr2 =
				new BinaryExpression(location, Operator.COMPGT, operation, signedBitLengthLiteral);

		final Expression expr =
				isSigned ? new UnaryExpression(location, UnaryExpression.Operator.ARITHNEGATIVE, signedBitLengthLiteral)
						: new IntegerLiteral(location, "0");
		final BinaryExpression binaryExpr3 = new BinaryExpression(location, Operator.ARITHPLUS, operation, expr);

		final BinaryExpression binaryExpr4 = new BinaryExpression(location, Operator.LOGICOR, binaryExpr2, binaryExpr3);
		fieldValues[1] = binaryExpr4;

		final StructConstructor structConstructor = new StructConstructor(location, fieldIdentifiers, fieldValues);
		final VariableLHS varLhs = new VariableLHS(location, Identifier);
		final AssignmentStatement assignmentStmt = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
				new Expression[] { structConstructor });

		return new Pair<>(varDec, assignmentStmt);
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
		final LLVMIRParser.ConcreteTypeContext typeContext =
				instructionType.addInst().typeValue().firstClassType().concreteType();
		result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
		final int bitLength = getBitLengthFromType(typeContext);
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final Expression leftExpr = constructExpressionFromValue(instructionType.addInst().typeValue().value(),
				typeContext, location, false);
		final Expression rightExpr =
				constructExpressionFromValue(instructionType.addInst().value(), typeContext, location, false);
		final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHPLUS, leftExpr, rightExpr);
		final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
		final BinaryExpression signedExpr =
				new BinaryExpression(location, Operator.ARITHMOD, binaryExpr, bitLengthLiteral);
		final AssignmentStatement assignment =
				new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { signedExpr });
		result.addFuncBlock(assignment);
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
		final LLVMIRParser.ConcreteTypeContext typeContext =
				instructionType.subInst().typeValue().firstClassType().concreteType();
		result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
		final int bitLength = getBitLengthFromType(typeContext);
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final Expression leftExpr = constructExpressionFromValue(instructionType.subInst().typeValue().value(),
				typeContext, location, false);
		final Expression rightExpr =
				constructExpressionFromValue(instructionType.subInst().value(), typeContext, location, false);
		final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMINUS, leftExpr, rightExpr);
		final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
		final BinaryExpression signedExpr =
				new BinaryExpression(location, Operator.ARITHMOD, binaryExpr, bitLengthLiteral);
		final AssignmentStatement assignment =
				new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { signedExpr });
		result.addFuncBlock(assignment);
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
		final LLVMIRParser.ConcreteTypeContext typeContext =
				instructionType.mulInst().typeValue().firstClassType().concreteType();
		result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
		final int bitLength = getBitLengthFromType(typeContext);
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final Expression leftExpr = constructExpressionFromValue(instructionType.mulInst().typeValue().value(),
				typeContext, location, false);
		final Expression rightExpr =
				constructExpressionFromValue(instructionType.mulInst().value(), typeContext, location, false);
		final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMUL, leftExpr, rightExpr);
		final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
		final BinaryExpression signedExpr =
				new BinaryExpression(location, Operator.ARITHMOD, binaryExpr, bitLengthLiteral);
		final AssignmentStatement assignment =
				new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { signedExpr });
		result.addFuncBlock(assignment);
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
		final LLVMIRParser.ConcreteTypeContext typeContext =
				instructionType.uDivInst().typeValue().firstClassType().concreteType();
		result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
		final int bitLength = getBitLengthFromType(typeContext);
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final Expression leftExpr = constructExpressionFromValue(instructionType.uDivInst().typeValue().value(),
				typeContext, location, false);
		final Expression rightExpr =
				constructExpressionFromValue(instructionType.uDivInst().value(), typeContext, location, false);
		final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHDIV, leftExpr, rightExpr);
		final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
		final BinaryExpression signedExpr =
				new BinaryExpression(location, Operator.ARITHMOD, binaryExpr, bitLengthLiteral);
		final AssignmentStatement assignment =
				new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { signedExpr });
		result.addFuncBlock(assignment);
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
		final LLVMIRParser.ConcreteTypeContext typeContext =
				instructionType.uRemInst().typeValue().firstClassType().concreteType();
		result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
		final int bitLength = getBitLengthFromType(typeContext);
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final Expression leftExpr = constructExpressionFromValue(instructionType.uRemInst().typeValue().value(),
				typeContext, location, false);
		final Expression rightExpr =
				constructExpressionFromValue(instructionType.uRemInst().value(), typeContext, location, false);
		final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMOD, leftExpr, rightExpr);
		final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
		final BinaryExpression signedExpr =
				new BinaryExpression(location, Operator.ARITHMOD, binaryExpr, bitLengthLiteral);
		final AssignmentStatement assignment =
				new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { signedExpr });
		result.addFuncBlock(assignment);
	}

	/**
	 * Constructs the local variable and the assignment for an integer comparison (icmp instruction).
	 *
	 * The comparison is a Boogie Boolean. For signed relational predicates on integer types other than i1, both
	 * operands are converted to signed values first.
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
	public static void handleICmpInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		result.addFuncLocalVar(constructVarDecFromString("bool", identifier, location));
		final LLVMIRParser.ConcreteTypeContext typeContext =
				instructionType.iCmpInst().typeValue().firstClassType().concreteType();

		Expression leftExpr = null;
		Expression rightExpr = null;
		final String operatorString = instructionType.iCmpInst().iPred().getText();
		final Operator operator = getCompOperatorFromOperatorValue(operatorString);
		final boolean isSigned = operatorString.startsWith("s");

		final LLVMIRParser.ValueContext leftValue = instructionType.iCmpInst().typeValue().value();
		leftExpr = constructExpressionFromValue(leftValue, typeContext, location, isSigned);

		final LLVMIRParser.ValueContext rightValue = instructionType.iCmpInst().value();
		rightExpr = constructExpressionFromValue(rightValue, typeContext, location, isSigned);

		if (isSigned && typeContext.intType() != null && !typeContext.intType().getText().equals("i1")) {
			final int bitLength = getBitLengthFromType(typeContext);
			if (operator == Operator.COMPLEQ || operator == Operator.COMPLT || operator == Operator.COMPGEQ
					|| operator == Operator.COMPGT) {
				leftExpr = constructSignedExpression(leftExpr, bitLength, location);
				rightExpr = constructSignedExpression(rightExpr, bitLength, location);
			}
		}

		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final BinaryExpression binaryExpr = new BinaryExpression(location, operator, leftExpr, rightExpr);
		final AssignmentStatement assignment =
				new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { binaryExpr });
		result.addFuncBlock(assignment);
	}
}