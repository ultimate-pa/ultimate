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

import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;
import de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.Result;

/**
 * Builders for the Boogie statements of the bitwise instructions of LLVM-IR.
 *
 * All methods only work on their parameters and do not access any state of the translation.
 */
public final class BitwiseInstructionHandler {

	private BitwiseInstructionHandler() {
		// utility class, not meant to be instantiated
	}

	/**
	 * Constructs a havoc statement for bitwise instructions.
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
	 * @param reason
	 *            The reason for the overapproximation.
	 * @param identifier
	 *            The identifier for the local variable to be constructed.
	 */
	private static void constructHavocStatementFromTypeValue(final Result result,
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
	 * Constructs the local variable and a havoc statement for an and instruction.
	 *
	 * @param result
	 *            The result to which the local variable and the havoc statement are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handleAndInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		constructHavocStatementFromTypeValue(result, instructionType.andInst().typeValue(), location, identifier,
				"andInst");
	}

	/**
	 * Constructs the local variable and a havoc statement for an or instruction.
	 *
	 * @param result
	 *            The result to which the local variable and the havoc statement are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handleOrInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		constructHavocStatementFromTypeValue(result, instructionType.orInst().typeValue(), location, identifier,
				"orInst");
	}

	/**
	 * Constructs the local variable and a havoc statement for a xor instruction.
	 *
	 * @param result
	 *            The result to which the local variable and the havoc statement are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handleXorInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		constructHavocStatementFromTypeValue(result, instructionType.xorInst().typeValue(), location, identifier,
				"xorInst");
	}

	/**
	 * Constructs the local variable and a havoc statement for a shl instruction.
	 *
	 * @param result
	 *            The result to which the local variable and the havoc statement are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handleShlInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		constructHavocStatementFromTypeValue(result, instructionType.shlInst().typeValue(), location, identifier,
				"shlInst");
	}

	/**
	 * Constructs the local variable and a havoc statement for an ashr instruction.
	 *
	 * @param result
	 *            The result to which the local variable and the havoc statement are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handleAShrInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		constructHavocStatementFromTypeValue(result, instructionType.aShrInst().typeValue(), location, identifier,
				"aShrInst");
	}

	/**
	 * Constructs the local variable and a havoc statement for a lshr instruction.
	 *
	 * @param result
	 *            The result to which the local variable and the havoc statement are added.
	 * @param instructionType
	 *            The value instruction context from the LLVM IR parse tree.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handleLShrInst(final Result result, final LLVMIRParser.ValueInstructionContext instructionType,
			final String identifier, final LlvmirLocation location) {
		constructHavocStatementFromTypeValue(result, instructionType.lShrInst().typeValue(), location, identifier,
				"lShrInst");
	}
}