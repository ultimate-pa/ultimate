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

import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.constructVarDecFromTypeContext;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructExpressionFromValue;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;
import de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.Result;

/**
 * Builders for the Boogie statements of the select and extractvalue instructions of LLVM-IR.
 *
 * All methods only work on their parameters and do not access any state of the translation.
 */
public final class OtherInstructionHandler {

	private OtherInstructionHandler() {
		// utility class, not meant to be instantiated
	}

	/**
	 * Constructs the local variable and the if statement for a select instruction.
	 *
	 * The local variable is assigned the second operand if the condition (first operand) holds and the third operand
	 * otherwise.
	 *
	 * @param result
	 *            The result to which the local variable and the if statement are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handleSelectInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		final LLVMIRParser.ConcreteTypeContext typeContext0 =
				instructionType.selectInst().typeValue(0).firstClassType().concreteType();
		final LLVMIRParser.ConcreteTypeContext typeContext1 =
				instructionType.selectInst().typeValue(1).firstClassType().concreteType();

		final Expression ifExpr = constructExpressionFromValue(instructionType.selectInst().typeValue(0).value(),
				typeContext0, location, false);
		final Expression thenExpr = constructExpressionFromValue(instructionType.selectInst().typeValue(1).value(),
				typeContext1, location, false);
		final Expression elseExpr = constructExpressionFromValue(instructionType.selectInst().typeValue(2).value(),
				typeContext1, location, false);
		result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext1, identifier, location));
		final VariableLHS thenVarLhs = new VariableLHS(location, identifier);
		final VariableLHS elseVarLhs = new VariableLHS(location, identifier);
		final AssignmentStatement thenAssignment =
				new AssignmentStatement(location, new LeftHandSide[] { thenVarLhs }, new Expression[] { thenExpr });
		final AssignmentStatement elseAssignment =
				new AssignmentStatement(location, new LeftHandSide[] { elseVarLhs }, new Expression[] { elseExpr });
		final IfStatement ifStmt = new IfStatement(location, ifExpr, new Statement[] { thenAssignment },
				new Statement[] { elseAssignment });
		result.addFuncBlock(ifStmt);
	}

	/**
	 * Constructs the local variable and the assignment for an extractvalue instruction.
	 *
	 * Only values of a struct type are supported. The assigned value is the struct field at the given index.
	 *
	 * @param result
	 *            The result to which the local variable and the assignment are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 * @throws AssertionError
	 *             if the value is not of a struct type.
	 */
	public static void handleExtractValueInst(final Result result,
			final LLVMIRParser.ValueInstructionContext instructionType, final String identifier,
			final LlvmirLocation location) throws AssertionError {
		if (instructionType.extractValueInst().typeValue().firstClassType().concreteType().structType() == null) {
			throw new AssertionError(
					"The support for extractValue instructions without a struct type is not implemented yet.");
		}
		final int indexNumber = Integer.parseInt(instructionType.extractValueInst().IntLit(0).toString());
		final LLVMIRParser.TypeContext typeContext = instructionType.extractValueInst().typeValue().firstClassType()
				.concreteType().structType().type(indexNumber);
		final VariableDeclaration varDecl = (constructVarDecFromTypeContext(typeContext, identifier, location));
		result.addFuncLocalVar(varDecl);
		final StructAccessExpression structAccessExpr = new StructAccessExpression(location,
				constructExpressionFromValue(instructionType.extractValueInst().typeValue().value(),
						instructionType.extractValueInst().typeValue().firstClassType().concreteType(), location,
						false),
				String.valueOf(indexNumber));
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final AssignmentStatement assignment =
				new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { structAccessExpr });
		result.addFuncBlock(assignment);
	}
}