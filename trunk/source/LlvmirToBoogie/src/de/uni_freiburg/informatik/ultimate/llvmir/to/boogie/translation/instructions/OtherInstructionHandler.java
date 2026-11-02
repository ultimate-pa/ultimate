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
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.LABEL_IDENTIFIER;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructExpressionFromValue;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructSignedExpression;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.getBitLengthFromType;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.getCompOperatorFromOperatorValue;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.getLabelIndexFromFuncBody;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.unifyIdentifier;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;
import de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.Result;

/**
 * Builders for the Boogie statements of the select, icmp and phi instructions of LLVM-IR.
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

	/**
	 * Constructs the local variable and the statements for a phi instruction.
	 *
	 * For each incoming value the local variable is assigned this value if the last visited label is the one of the
	 * incoming block.
	 *
	 * @param result
	 *            The result to which the local variable and the statements are added.
	 * @param ctx
	 *            The parse tree context for the local variable definition.
	 * @param identifier
	 *            The identifier of the local variable that receives the result.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 */
	public static void handlePhiInst(final Result result, final LLVMIRParser.LocalDefInstContext ctx,
			final String identifier, final LlvmirLocation location) {
		final LLVMIRParser.ValueInstructionContext instructionType = ctx.valueInstruction();
		final LLVMIRParser.TypeContext typeContext = instructionType.phiInst().type();
		result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
		for (final LLVMIRParser.IncContext inc : instructionType.phiInst().inc()) {
			final String incIdentifier = unifyIdentifier(inc.LocalIdent().getText());
			final int labelIndex = getLabelIndexFromFuncBody(ctx, incIdentifier);
			final IdentifierExpression incExpr = new IdentifierExpression(location, LABEL_IDENTIFIER);
			final IntegerLiteral labelIndexLiteral = new IntegerLiteral(location, Integer.toString(labelIndex));
			final BinaryExpression binaryExpr =
					new BinaryExpression(location, Operator.COMPEQ, incExpr, labelIndexLiteral);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { constructExpressionFromValue(inc.value(), typeContext, location, false) });
			final IfStatement ifStmt =
					new IfStatement(location, binaryExpr, new Statement[] { assignment }, new Statement[] {});
			result.addFuncBlock(ifStmt);
		}
	}
}