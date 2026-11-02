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

import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.VariableDeclarationBuilder.constructVarDecFromString;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.VariableDeclarationBuilder.constructVarDecFromTypeContext;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructBitLengthLiteral;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructExpressionFromValue;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructSignedExpression;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.getBitLengthFromType;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;
import de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.Result;

/**
 * Builders for the Boogie statements of integer conversion instructions of LLVM-IR.
 *
 * All methods only work on their parameters and do not access any state of the translation.
 */
public final class ConversionInstructionHandler {

	private ConversionInstructionHandler() {
		// utility class, not meant to be instantiated
	}

	/**
	 * Constructs the local variable and the assignment for an integer truncation (trunc instruction).
	 *
	 * A truncation to one bit is true if the value modulo 2 is 1. Otherwise the value is taken modulo 2^newBitLength.
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
	public static void handleTruncInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		final LLVMIRParser.TypeContext newTypeContext = instructionType.truncInst().type();
		final LLVMIRParser.ConcreteTypeContext oldTypeContext =
				instructionType.truncInst().typeValue().firstClassType().concreteType();
		final int newBitLength = getBitLengthFromType(newTypeContext);
		final VariableDeclaration varDecl = (constructVarDecFromTypeContext(newTypeContext, identifier, location));
		result.addFuncLocalVar(varDecl);
		if (newBitLength == 1) {
			final IntegerLiteral oneLiteral = new IntegerLiteral(location, "1");
			final IntegerLiteral twoLiteral = new IntegerLiteral(location, "2");
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMOD,
					constructExpressionFromValue(instructionType.truncInst().typeValue().value(), oldTypeContext,
							location, false),
					twoLiteral);
			final BinaryExpression conditionalExpr =
					new BinaryExpression(location, Operator.COMPEQ, binaryExpr, oneLiteral);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { conditionalExpr });
			result.addFuncBlock(assignment);
		} else {
			final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, newBitLength, false);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMOD,
					constructExpressionFromValue(instructionType.truncInst().typeValue().value(), oldTypeContext,
							location, false),
					bitLengthLiteral);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final AssignmentStatement assignment =
					new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { binaryExpr });
			result.addFuncBlock(assignment);
		}
	}

	/**
	 * Constructs the local variable and the assignment for a zero extension (zext instruction).
	 *
	 * An i1 value is converted to 1 or 0 with an if statement. Other values are assigned unchanged.
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
	public static void handleZExtInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		result.addFuncLocalVar(constructVarDecFromString("int", identifier, location));
		final LLVMIRParser.ConcreteTypeContext typeContext =
				instructionType.zExtInst().typeValue().firstClassType().concreteType();
		if (typeContext.intType().getText().equals("i1")) {
			final IntegerLiteral zeroLiteral = new IntegerLiteral(location, "0");
			final IntegerLiteral oneLiteral = new IntegerLiteral(location, "1");
			final VariableLHS zeroVarLhs = new VariableLHS(location, identifier);
			final VariableLHS oneVarLhs = new VariableLHS(location, identifier);
			final AssignmentStatement elseAssignment = new AssignmentStatement(location,
					new LeftHandSide[] { zeroVarLhs }, new Expression[] { zeroLiteral });
			final AssignmentStatement thenAssignment = new AssignmentStatement(location,
					new LeftHandSide[] { oneVarLhs }, new Expression[] { oneLiteral });
			final IfStatement ifStmt =
					new IfStatement(location,
							constructExpressionFromValue(instructionType.zExtInst().typeValue().value(), typeContext,
									location, false),
							new Statement[] { thenAssignment }, new Statement[] { elseAssignment });
			result.addFuncBlock(ifStmt);
		} else {
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { constructExpressionFromValue(instructionType.zExtInst().typeValue().value(),
							typeContext, location, false) });
			result.addFuncBlock(assignment);
		}
	}

	/**
	 * Constructs the local variable and the assignment for a sign extension (sext instruction).
	 *
	 * An i1 value is converted to 1 or 0 with an if statement. For other values the signed value is taken modulo
	 * 2^newBitLength.
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
	public static void handleSExtInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		final LLVMIRParser.TypeContext newTypeContext = instructionType.sExtInst().type();
		final LLVMIRParser.ConcreteTypeContext oldTypeContext =
				instructionType.sExtInst().typeValue().firstClassType().concreteType();
		final String oldTypeString = oldTypeContext.intType().getText();
		result.addFuncLocalVar(constructVarDecFromTypeContext(newTypeContext, identifier, location));
		if (oldTypeContext.intType() != null && oldTypeString.equals("i1")) {
			final IntegerLiteral zeroLiteral = new IntegerLiteral(location, "0");
			final IntegerLiteral oneLiteral = new IntegerLiteral(location, "1");
			final VariableLHS zeroVarLhs = new VariableLHS(location, identifier);
			final VariableLHS oneVarLhs = new VariableLHS(location, identifier);
			final AssignmentStatement elseAssignment = new AssignmentStatement(location,
					new LeftHandSide[] { zeroVarLhs }, new Expression[] { zeroLiteral });
			final AssignmentStatement thenAssignment = new AssignmentStatement(location,
					new LeftHandSide[] { oneVarLhs }, new Expression[] { oneLiteral });
			final IfStatement ifStmt = new IfStatement(
					location, constructExpressionFromValue(instructionType.sExtInst().typeValue().value(),
							oldTypeContext, location, false),
					new Statement[] { thenAssignment }, new Statement[] { elseAssignment });
			result.addFuncBlock(ifStmt);
		} else {
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final int oldBitLength = getBitLengthFromType(oldTypeContext);
			final int newBitLength = getBitLengthFromType(newTypeContext);
			final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, newBitLength, false);
			final BinaryExpression binaryExpr =
					new BinaryExpression(location, Operator.ARITHMOD,
							constructSignedExpression(constructExpressionFromValue(
									instructionType.sExtInst().typeValue().value(), oldTypeContext, location, false),
									oldBitLength, location),
							bitLengthLiteral);
			final AssignmentStatement assignment =
					new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { binaryExpr });
			result.addFuncBlock(assignment);
		}
	}
}