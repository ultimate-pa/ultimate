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
package de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation;

import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.constructCDivFunction;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.constructProcedureFromFuncDef;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.constructVarDecFromString;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.contructRemainderFunction;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.procedureAlreadyPresent;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.InitialDeclarationBuilder.constructInitialDeclarations;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleAddInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleICmpInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleMulInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleSDivInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleSRemInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleSubInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleUDivInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleURemInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.BitwiseInstructionHandler.handleAShrInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.BitwiseInstructionHandler.handleAndInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.BitwiseInstructionHandler.handleLShrInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.BitwiseInstructionHandler.handleOrInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.BitwiseInstructionHandler.handleShlInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.BitwiseInstructionHandler.handleXorInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.CallInstructionHandler.handleCallInstWithResult;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.CallInstructionHandler.handleCallInstWithoutResult;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ControlFlowInstructionHandler.handleBrTerm;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ControlFlowInstructionHandler.handleCondBrTerm;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ControlFlowInstructionHandler.handlePhiInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ControlFlowInstructionHandler.handleRetTerm;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ControlFlowInstructionHandler.handleSwitchTerm;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ConversionInstructionHandler.handleSExtInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ConversionInstructionHandler.handleTruncInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ConversionInstructionHandler.handleZExtInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.MemoryInstructionHandler.handleAllocaInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.MemoryInstructionHandler.handleLoadInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.MemoryInstructionHandler.handleStoreInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.OtherInstructionHandler.handleExtractValueInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.OtherInstructionHandler.handleSelectInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.LABEL_IDENTIFIER;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.UNDEF_IDENTIFIER;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructExpressionFromConstant;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructLabelAssignment;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.unifyIdentifier;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRBaseVisitor;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class LlvmirToBoogieVisitor extends LLVMIRBaseVisitor<Result> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private Unit mResult;
	private final String mFilename;
	private LlvmirLocation mLocation;

	private final ArrayList<Declaration> mDeclarations = new ArrayList<>();
	private final HashMap<String, Pair<Declaration, Statement>> mGlobalVars = new HashMap<>();

	public LlvmirToBoogieVisitor(final IUltimateServiceProvider services, final ILogger logger, final String filename) {
		assert services != null;
		mServices = services;
		mLogger = logger;
		mResult = null;
		mFilename = filename;
		mLocation = null;
		mLogger.info("Starting translation of LLVM IR to Boogie for file: " + mFilename);
	}

	public Unit getResult() {
		if (mResult == null) {
			mLogger.error("Translation result is null. Ensure that visitCompilationUnit was called successfully.");
			throw new IllegalStateException("Translation result is null");
		}
		return mResult;
	}

	/**
	 * Constructs a location object from the given context.
	 *
	 * This method creates a LlvmirLocation object that represents the location of a specific context in the source
	 * code. It uses the filename, line numbers, and character positions from the context to create the location.
	 *
	 * @param ctx
	 *            The ParserRuleContext from which to extract the location information.
	 * @return A LlvmirLocation object representing the location in the source code.
	 */
	private LlvmirLocation constructLocation(final ParserRuleContext ctx) {
		return new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());
	}

	/**
	 * Handles the visit event for the compilation unit in the LLVM IR parse tree.
	 *
	 * This method initializes the location and processes the children of the compilation unit context to construct
	 * declarations and the final Boogie AST unit.
	 *
	 * @param ctx
	 *            The parse tree context for the compilation unit.
	 * @return A Result object containing the final Boogie AST unit.
	 */
	@Override
	public Result visitCompilationUnit(final LLVMIRParser.CompilationUnitContext ctx) {
		mLocation = constructLocation(ctx);
		mDeclarations.add(constructCDivFunction(mLocation));
		mDeclarations.add(contructRemainderFunction(mLocation));

		ParseTree mainFunc = null;

		for (final ParseTree child : ctx.children) {
			if (!(child.getChild(0) instanceof LLVMIRParser.FuncDefContext)) {
				visit(child); // visit non-function definitions immediately
				continue;
			}

			final LLVMIRParser.FuncDefContext funcDef = (LLVMIRParser.FuncDefContext) child.getChild(0);
			final String funcName = funcDef.funcHeader().GlobalIdent().getText();

			if ("@main".equals(funcName)) {
				mainFunc = child;
			} else {
				visit(child); // visit non-main immediately
			}
		}

		// process main last
		if (mainFunc != null) {
			visit(mainFunc);
		}

		constructInitialDeclarations(mDeclarations, mGlobalVars, mLocation, mLogger);
		mResult = new Unit(mLocation, mDeclarations.toArray(Declaration[]::new));
		return null;
	}

	/**
	 * Handles the visit event for a function definition in the LLVM IR parse tree.
	 *
	 * This method translates the parsed LLVM IR function into a Boogie procedure, including its body, parameters, and
	 * return type. Currently, only `void` and integer return types are supported.
	 *
	 * @param ctx
	 *            The parse tree context for the function definition.
	 * @throws AssertionError
	 *             if the return type is not supported.
	 */
	@Override
	public Result visitFuncDef(final LLVMIRParser.FuncDefContext ctx) throws AssertionError {
		final Result result = new Result();

		result.addFuncLocalVar(constructVarDecFromString("int", UNDEF_IDENTIFIER, mLocation));
		final VariableLHS undefVar = new VariableLHS(mLocation, UNDEF_IDENTIFIER);
		final HavocStatement havocStmt = new HavocStatement(mLocation, new VariableLHS[] { undefVar });
		result.addFuncBlock(havocStmt);

		for (final ParseTree child : ctx.children) {
			final Result childResult = child.accept(this);
			if (childResult != null) {
				result.merge(childResult);
			}
		}

		result.addFuncLocalVar(constructVarDecFromString("int", LABEL_IDENTIFIER, mLocation));
		final LlvmirLocation location = constructLocation(ctx);
		final Procedure procedure = constructProcedureFromFuncDef(ctx, result, location);

		if (!procedureAlreadyPresent(procedure, mDeclarations)) {
			mDeclarations.add(procedure);
		}

		return null;
	}

	/**
	 * Handles the visit event for a function body in the LLVM IR parse tree.
	 *
	 * This method processes the children of the function body context and merges their results into a single Result
	 * object.
	 *
	 * @param ctx
	 *            The parse tree context for the function body.
	 * @return A Result object containing the merged results of the children.
	 */
	@Override
	public Result visitFuncBody(final LLVMIRParser.FuncBodyContext ctx) {
		final Result result = new Result();
		for (final LLVMIRParser.BasicBlockContext childCtx : ctx.basicBlock()) {
			final Result childResult = visit(childCtx);
			if (childResult != null) {
				result.merge(childResult);
			}
		}
		return result;
	}

	/**
	 * Handles the visit event for a basic block in the LLVM IR parse tree.
	 *
	 * This method processes the basic block context, constructs a label for it, and processes its children to generate
	 * statements for the Boogie AST. It also handles terminators like conditional and unconditional branches.
	 *
	 * @param ctx
	 *            The parse tree context for the basic block.
	 * @return A Result object containing the generated statements for the basic block.
	 */
	@Override
	public Result visitBasicBlock(final LLVMIRParser.BasicBlockContext ctx) {
		final LlvmirLocation location = constructLocation(ctx);
		final Result result = new Result();

		final LLVMIRParser.FuncBodyContext funcBodyCtx = (LLVMIRParser.FuncBodyContext) ctx.getParent();
		final List<LLVMIRParser.BasicBlockContext> blocks = funcBodyCtx.basicBlock();
		final int index = blocks.indexOf(ctx);

		final String labelName = unifyIdentifier(ctx.LabelIdent().getText());
		final Label label = new Label(location, labelName, new NamedAttribute[] {});
		result.addFuncBlock(label);

		for (final ParseTree child : ctx.children) {
			// If the child is a branching term (CondBrTerm or BrTerm), we add an assignment to the label variable, it
			// is necessary to know the last visited label to properly handle phi instructions.
			if (child.getChild(0) instanceof LLVMIRParser.CondBrTermContext
					|| child.getChild(0) instanceof LLVMIRParser.BrTermContext) {
				result.addFuncBlock(constructLabelAssignment(location, index));
			}
			final Result childResult = child.accept(this);
			if (childResult != null) {
				result.merge(childResult);
			}
		}

		// If this is not the last block, we add an assignment to the label variable, it is necessary to know the last
		// visited label to properly handle phi instructions.
		if (!(index == blocks.size() - 1)) {
			result.addFuncBlock(constructLabelAssignment(location, index));
		}

		return result;
	}

	/**
	 * Handles the visit event for a return term in the LLVM IR parse tree.
	 *
	 * This method processes the return statement, handling both void returns and returns with values. It constructs
	 * appropriate Boogie statements based on the return type.
	 *
	 * @param ctx
	 *            The parse tree context for the return term.
	 * @return A Result object containing the generated statements for the return term.
	 * @throws AssertionError
	 *             if the return type is not supported.
	 */
	@Override
	public Result visitRetTerm(final LLVMIRParser.RetTermContext ctx) throws AssertionError {
		return handleRetTerm(ctx, constructLocation(ctx));
	}

	/**
	 * Handles the visit event for a global variable definition in the LLVM IR parse tree.
	 *
	 * This method translates the global variable definition into a Boogie variable declaration and initializes it based
	 * on the type of the constant value.
	 *
	 * @param ctx
	 *            The parse tree context for the global variable definition.
	 * @return A Result object containing the variable declaration and initialization statements.
	 * @throws AssertionError
	 *             if the type is not supported.
	 */
	@Override
	public Result visitGlobalDef(final LLVMIRParser.GlobalDefContext ctx) throws AssertionError {
		final LLVMIRParser.TypeContext type = ctx.type();
		final String identifier = unifyIdentifier(ctx.GlobalIdent().getText());
		final LlvmirLocation location = constructLocation(ctx);

		if (type.intType() == null) {
			throw new AssertionError("The support for types other than integers is not implemented yet.");
		}

		final String typeString = type.intType().getText().equals("i1") ? "bool" : "int";
		final VariableDeclaration varDecl = constructVarDecFromString(typeString, identifier, location);

		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
				new Expression[] { constructExpressionFromConstant(ctx.constant(), type, location, false) });

		mGlobalVars.put(identifier, new Pair<>(varDecl, assignment));

		return null;
	}

	/**
	 * Handles the visit event for a local variable definition in the LLVM IR parse tree.
	 *
	 * This method translates the local variable definition into a Boogie variable declaration and initializes it based
	 * on the type of instruction.
	 *
	 * @param ctx
	 *            The parse tree context for the local variable definition.
	 * @throws AssertionError
	 *             if the instruction type is not supported.
	 */
	@Override
	public Result visitLocalDefInst(final LLVMIRParser.LocalDefInstContext ctx) {
		final Result result = new Result();
		final String identifier = unifyIdentifier(ctx.LocalIdent().getText());
		final LLVMIRParser.ValueInstructionContext instructionType = ctx.valueInstruction();
		final LlvmirLocation location = constructLocation(ctx);

		if (instructionType.loadInst() != null) {
			handleLoadInst(result, instructionType, identifier, location);
		} else if (instructionType.iCmpInst() != null) {
			handleICmpInst(result, instructionType, identifier, location);
		} else if (instructionType.phiInst() != null) {
			handlePhiInst(result, ctx, identifier, location);
		} else if (instructionType.zExtInst() != null) {
			handleZExtInst(result, instructionType, identifier, location);
		} else if (instructionType.sExtInst() != null) {
			handleSExtInst(result, instructionType, identifier, location);
		} else if (instructionType.addInst() != null) {
			handleAddInst(result, instructionType, identifier, location);
		} else if (instructionType.sDivInst() != null) {
			handleSDivInst(result, instructionType, identifier, location);
		} else if (instructionType.uDivInst() != null) {
			handleUDivInst(result, instructionType, identifier, location);
		} else if (instructionType.uRemInst() != null) {
			handleURemInst(result, instructionType, identifier, location);
		} else if (instructionType.sRemInst() != null) {
			handleSRemInst(result, instructionType, identifier, location, mLocation);
		} else if (instructionType.subInst() != null) {
			handleSubInst(result, instructionType, identifier, location);
		} else if (instructionType.mulInst() != null) {
			handleMulInst(result, instructionType, identifier, location);
		} else if (instructionType.allocaInst() != null) {
			handleAllocaInst(result, instructionType, identifier, location);
		} else if (instructionType.callInst() != null) {
			handleCallInstWithResult(result, instructionType, identifier, location, mDeclarations);
		} else if (instructionType.selectInst() != null) {
			handleSelectInst(result, instructionType, identifier, location);
		} else if (instructionType.truncInst() != null) {
			handleTruncInst(result, instructionType, identifier, location);
		} else if (instructionType.extractValueInst() != null) {
			handleExtractValueInst(result, instructionType, identifier, location);
		} else if (instructionType.andInst() != null) {
			handleAndInst(result, instructionType, identifier, location);
		} else if (instructionType.orInst() != null) {
			handleOrInst(result, instructionType, identifier, location);
		} else if (instructionType.xorInst() != null) {
			handleXorInst(result, instructionType, identifier, location);
		} else if (instructionType.shlInst() != null) {
			handleShlInst(result, instructionType, identifier, location);
		} else if (instructionType.aShrInst() != null) {
			handleAShrInst(result, instructionType, identifier, location);
		} else if (instructionType.lShrInst() != null) {
			handleLShrInst(result, instructionType, identifier, location);
		} else {
			throw new AssertionError("The support for the given instruction is not implemented yet.");
		}
		return result;
	}

	/**
	 * Handles the visit event for a branch terminator in the LLVM IR parse tree.
	 *
	 * This method processes the branch terminator and constructs a GotoStatement to jump to the specified label.
	 *
	 * @param ctx
	 *            The parse tree context for the branch terminator.
	 * @return A Result object containing the GotoStatement.
	 */
	@Override
	public Result visitBrTerm(final LLVMIRParser.BrTermContext ctx) {
		return handleBrTerm(ctx, constructLocation(ctx));
	}

	/**
	 * Handles the visit event for a conditional branch terminator in the LLVM IR parse tree.
	 *
	 * This method processes the conditional branch terminator and constructs an IfStatement to handle the condition,
	 * along with GotoStatements for the true and false branches.
	 *
	 * @param ctx
	 *            The parse tree context for the conditional branch terminator.
	 * @return A Result object containing the IfStatement and GotoStatements.
	 */
	@Override
	public Result visitCondBrTerm(final LLVMIRParser.CondBrTermContext ctx) {
		return handleCondBrTerm(ctx, constructLocation(ctx));
	}

	/**
	 * Handles the visit event for a store instruction in the LLVM IR parse tree.
	 *
	 * This method processes the store instruction and constructs an AssignmentStatement to assign a value to a
	 * variable.
	 *
	 * @param ctx
	 *            The parse tree context for the store instruction.
	 * @return A Result object containing the AssignmentStatement.
	 */
	@Override
	public Result visitStoreInst(final LLVMIRParser.StoreInstContext ctx) {
		return handleStoreInst(ctx, constructLocation(ctx));
	}

	/**
	 * Handles the visit event for a call instruction in the LLVM IR parse tree.
	 *
	 * This method processes the call instruction and constructs a CallStatement or an AssertStatement based on the
	 * called function.
	 *
	 * @param ctx
	 *            The parse tree context for the call instruction.
	 * @return A Result object containing the CallStatement or AssertStatement.
	 */
	@Override
	public Result visitCallInst(final LLVMIRParser.CallInstContext ctx) {
		return handleCallInstWithoutResult(ctx, constructLocation(ctx), mDeclarations);
	}

	/**
	 * Handles the visit event for a switch terminator in the LLVM IR parse tree.
	 *
	 * This method processes the switch terminator and constructs an IfStatement for each case, along with a
	 * GotoStatement for the default case.
	 *
	 * @param ctx
	 *            The parse tree context for the switch terminator.
	 * @return A Result object containing the IfStatements and GotoStatement.
	 */
	@Override
	public Result visitSwitchTerm(final LLVMIRParser.SwitchTermContext ctx) {
		return handleSwitchTerm(ctx, constructLocation(ctx));
	}
}