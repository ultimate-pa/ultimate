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

import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.LABEL_IDENTIFIER;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructExpressionFromConstant;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructExpressionFromValue;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.getEnclosingBasicBlock;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.getLabelIndexFromFuncBody;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.unifyIdentifier;

import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;
import de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.Result;

/**
 * Builders for the Boogie statements of the terminator instructions of LLVM-IR.
 *
 * All methods only work on their parameters and do not access any state of the translation.
 */
public final class TerminatorInstructionHandler {

	private TerminatorInstructionHandler() {
		// utility class, not meant to be instantiated
	}

	/**
	 * Constructs the statements for a return terminator.
	 *
	 * Void returns and returns with an integer value are supported.
	 *
	 * @param ctx
	 *            The parse tree context for the ret terminator.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 * @return A Result object containing the generated statements for the return term.
	 * @throws AssertionError
	 *             if the return type is not supported.
	 */
	public static Result handleRetTerm(final LLVMIRParser.RetTermContext ctx, final LlvmirLocation location)
			throws AssertionError {
		final Result result = new Result();

		if (ctx.value() == null) {
			// If there is no value, we assume a void return type
			final ReturnStatement returnStmt = new ReturnStatement(location);
			result.addFuncBlock(returnStmt);
		} else {
			final LLVMIRParser.ConcreteTypeContext returnType = ctx.concreteType();
			if (returnType.intType() == null) {
				throw new AssertionError("The support for return types other than integers is not implemented yet.");
			}
			final VariableLHS returnVar = new VariableLHS(location, "ret");
			final AssignmentStatement assignmentStmt = new AssignmentStatement(location,
					new LeftHandSide[] { returnVar },
					new Expression[] { constructExpressionFromValue(ctx.value(), returnType, location, false) });
			final ReturnStatement returnStmt = new ReturnStatement(location);
			result.addFuncBlocks(Arrays.asList(assignmentStmt, returnStmt));
		}
		return result;

	}

	/**
	 * Constructs the statements for a branch terminator.
	 *
	 * The branch is translated to a GotoStatement that jumps to the specified label.
	 *
	 * @param ctx
	 *            The parse tree context for the br terminator.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 * @return A Result object containing the GotoStatement.
	 */
	public static Result handleBrTerm(final LLVMIRParser.BrTermContext ctx, final LlvmirLocation location) {
		final Result result = new Result();
		final String labelIdentifier = unifyIdentifier(ctx.label().LocalIdent().getText());
		final GotoStatement gotoStmt = new GotoStatement(location, new String[] { labelIdentifier });
		result.addFuncBlock(gotoStmt);

		return result;
	}

	/**
	 * Constructs the statements for a conditional branch terminator.
	 *
	 * The branch is translated to an IfStatement with a GotoStatement for the true and for the false branch.
	 *
	 * @param ctx
	 *            The parse tree context for the condbr terminator.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 * @return A Result object containing the IfStatement and GotoStatements.
	 */
	public static Result handleCondBrTerm(final LLVMIRParser.CondBrTermContext ctx, final LlvmirLocation location) {
		final Result result = new Result();

		final String variableIdentifier = unifyIdentifier(ctx.value().LocalIdent().getText());
		final String thenLabelIdentifier = unifyIdentifier(ctx.label(0).LocalIdent().getText());
		final String elseLabelIdentifier = unifyIdentifier(ctx.label(1).LocalIdent().getText());
		final GotoStatement thenGoto = new GotoStatement(location, new String[] { thenLabelIdentifier });
		final GotoStatement elseGoto = new GotoStatement(location, new String[] { elseLabelIdentifier });
		final IdentifierExpression variableExpr = new IdentifierExpression(location, variableIdentifier);
		final IfStatement ifStmt =
				new IfStatement(location, variableExpr, new Statement[] { thenGoto }, new Statement[] { elseGoto });
		result.addFuncBlock(ifStmt);

		return result;
	}

	/**
	 * Constructs the statements for a switch terminator.
	 *
	 * Each case is translated to an IfStatement with a GotoStatement, followed by a GotoStatement for the default case.
	 *
	 * @param ctx
	 *            The parse tree context for the switch terminator.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 * @return A Result object containing the IfStatements and GotoStatement.
	 */
	public static Result handleSwitchTerm(final LLVMIRParser.SwitchTermContext ctx, final LlvmirLocation location) {
		final Result result = new Result();
		result.addFuncBlock(constructCurrentLabelAssignment(ctx, location));

		final LLVMIRParser.ConcreteTypeContext conditionTypeContext = ctx.typeValue().firstClassType().concreteType();
		final String typeIdentifier = conditionTypeContext.intType().getText().equals("i1") ? "bool" : "int";
		final List<LLVMIRParser.CaseContext> caseContexts = ctx.case_();
		if (typeIdentifier.equals("bool")) {
			result.addFuncBlock(constructBoolSwitchStatement(ctx, caseContexts, conditionTypeContext, location));
		} else {
			for (final LLVMIRParser.CaseContext caseContext : caseContexts) {
				result.addFuncBlock(constructCaseStatement(ctx, caseContext, conditionTypeContext, location));
			}
		}
		final String defaultLabelIdentifier = unifyIdentifier(ctx.label().LocalIdent().getText());
		final GotoStatement defaultGoto = new GotoStatement(location, new String[] { defaultLabelIdentifier });
		result.addFuncBlock(defaultGoto);
		return result;
	}

	/**
	 * Constructs the assignment of the index of the current basic block to the label variable.
	 *
	 * @param ctx
	 *            The parse tree context for the switch terminator.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 * @return The assignment statement.
	 */
	private static AssignmentStatement constructCurrentLabelAssignment(final LLVMIRParser.SwitchTermContext ctx,
			final LlvmirLocation location) {
		final LLVMIRParser.BasicBlockContext basicBlockContext = getEnclosingBasicBlock(ctx);
		final IntegerLiteral currentLabelLiteral = new IntegerLiteral(location, String
				.valueOf(getLabelIndexFromFuncBody(ctx, unifyIdentifier(basicBlockContext.LabelIdent().getText()))));
		final VariableLHS varLhs = new VariableLHS(location, LABEL_IDENTIFIER);
		return new AssignmentStatement(location, new LeftHandSide[] { varLhs },
				new Expression[] { currentLabelLiteral });
	}

	/**
	 * Constructs the if statement of a switch on a boolean condition: The first case is taken if the condition is
	 * false, the second case otherwise.
	 *
	 * @param ctx
	 *            The parse tree context for the switch terminator.
	 * @param caseContexts
	 *            The two cases of the switch.
	 * @param conditionTypeContext
	 *            The type of the condition.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 * @return The if statement with the two goto statements.
	 */
	private static IfStatement constructBoolSwitchStatement(final LLVMIRParser.SwitchTermContext ctx,
			final List<LLVMIRParser.CaseContext> caseContexts,
			final LLVMIRParser.ConcreteTypeContext conditionTypeContext, final LlvmirLocation location) {
		final String case0LabelIdentifier = unifyIdentifier(caseContexts.get(0).label().LocalIdent().getText());
		final String case1LabelIdentifier = unifyIdentifier(caseContexts.get(1).label().LocalIdent().getText());
		final GotoStatement thenGoto = new GotoStatement(location, new String[] { case0LabelIdentifier });
		final GotoStatement elseGoto = new GotoStatement(location, new String[] { case1LabelIdentifier });
		return new IfStatement(location,
				new UnaryExpression(location, UnaryExpression.Operator.LOGICNEG,
						constructExpressionFromValue(ctx.typeValue().value(), conditionTypeContext, location, false)),
				new Statement[] { thenGoto }, new Statement[] { elseGoto });
	}

	/**
	 * Constructs the if statement of one case of a switch on an integer condition: If the condition equals the constant
	 * of the case, the program jumps to the label of the case.
	 *
	 * @param ctx
	 *            The parse tree context for the switch terminator.
	 * @param caseContext
	 *            The case of the switch.
	 * @param conditionTypeContext
	 *            The type of the condition.
	 * @param location
	 *            The location in the source code where this instruction is defined.
	 * @return The if statement with the goto statement.
	 */
	private static IfStatement constructCaseStatement(final LLVMIRParser.SwitchTermContext ctx,
			final LLVMIRParser.CaseContext caseContext, final LLVMIRParser.ConcreteTypeContext conditionTypeContext,
			final LlvmirLocation location) {
		final LLVMIRParser.ConcreteTypeContext caseTypeContext =
				caseContext.typeConst().firstClassType().concreteType();
		final BinaryExpression conditionExpr = new BinaryExpression(location, Operator.COMPEQ,
				constructExpressionFromValue(ctx.typeValue().value(), conditionTypeContext, location, false),
				constructExpressionFromConstant(caseContext.typeConst().constant(), caseTypeContext, location, false));
		final String caseLabelIdentifier = unifyIdentifier(caseContext.label().LocalIdent().getText());
		final GotoStatement thenGoto = new GotoStatement(location, new String[] { caseLabelIdentifier });
		return new IfStatement(location, conditionExpr, new Statement[] { thenGoto }, new Statement[] {});
	}
}