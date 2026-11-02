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

import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.VariableDeclarationBuilder.constructVarDecFromTypeContext;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.ProcedureDeclerationBuilder.constructSpecFromIdentifier;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructExpressionFromValue;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.unifyIdentifier;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;
import de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.Result;

/**
 * Builders for the Boogie statements of memory instructions of LLVM-IR (load, alloca and store).
 *
 * All methods only work on their parameters and do not access any state of the translation.
 */
public final class MemoryInstructionHandler {

	private MemoryInstructionHandler() {
		// utility class, not meant to be instantiated
	}

	/**
	 * Constructs the local variable and the assignment for a load instruction.
	 *
	 * The loaded local or global variable is assigned to the new local variable.
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
	 *             if the type is not an integer type or the loaded value is not a variable.
	 */
	public static void handleLoadInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		final LLVMIRParser.TypeContext variableType = instructionType.loadInst().type();
		if (variableType.intType() == null) {
			throw new AssertionError(
					"The support for types other than integers in load instructions is not implemented yet.");
		}
		result.addFuncLocalVar(constructVarDecFromTypeContext(variableType, identifier, location));
		final VariableLHS varLhs = new VariableLHS(location, identifier);

		String loadVarIdentifier = null;
		if (instructionType.loadInst().typeValue().value().LocalIdent() != null) {
			loadVarIdentifier = unifyIdentifier(instructionType.loadInst().typeValue().value().LocalIdent().getText());
		} else if (instructionType.loadInst().typeValue().value().constant() != null) {
			loadVarIdentifier = instructionType.loadInst().typeValue().value().constant().GlobalIdent().getText();
		} else {
			throw new AssertionError("Something went wrong while parsing the load instruction:");
		}

		final IdentifierExpression loadVarExpr = new IdentifierExpression(location, unifyIdentifier(loadVarIdentifier));
		final AssignmentStatement assignment =
				new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { loadVarExpr });
		result.addFuncBlock(assignment);
	}

	/**
	 * Constructs the local variable for an alloca instruction.
	 *
	 * The allocated memory is represented by the local variable itself.
	 *
	 * @param result
	 *            The result to which the local variable is added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handleAllocaInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		final LLVMIRParser.TypeContext typeContext = instructionType.allocaInst().type();
		result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
	}

	/**
	 * Constructs the assignment for a store instruction.
	 *
	 * The stored value is assigned to the target variable. If the target is a global variable, it is added to the
	 * modified global variables of the result.
	 *
	 * @param ctx
	 *            The parse tree context for the store instruction.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 * @return A Result object containing the AssignmentStatement.
	 * @throws AssertionError
	 *             if the target of the store instruction is not a variable.
	 */
	public static Result handleStoreInst(final LLVMIRParser.StoreInstContext ctx, final LlvmirLocation location) {
		final Result result = new Result();

		String identifier = null;
		final LLVMIRParser.ValueContext valueContext1 = ctx.typeValue(1).value();
		if (valueContext1.LocalIdent() != null) {
			identifier = unifyIdentifier(ctx.typeValue(1).value().LocalIdent().getText());
		} else if (valueContext1.constant() != null) {
			identifier = unifyIdentifier(valueContext1.constant().GlobalIdent().getText());
			result.addFuncModifiedGlobalVar(constructSpecFromIdentifier(identifier, location));
		} else {
			throw new AssertionError("Something went wrong while parsing the store instruction:");
		}
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
				new Expression[] { constructExpressionFromValue(ctx.typeValue(0).value(),
						ctx.typeValue(0).firstClassType().concreteType(), location, false) });
		result.addFuncBlock(assignment);

		return result;
	}
}