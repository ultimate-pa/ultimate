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
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.constructInitialProcedure;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.constructSpecFromIdentifier;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.constructVarDecFromString;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.constructVarDecFromTypeContext;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.contructRemainderFunction;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.DeclarationBuilder.procedureAlreadyPresent;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.constructHavocStatementFromTypeValue;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleAddInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleICmpInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleMulInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleSDivInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleSRemInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleSubInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleUDivInst;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.instructions.ArithmeticInstructionHandler.handleURemInst;
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
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.LABEL_IDENTIFIER;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.UNDEF_IDENTIFIER;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructExpressionFromConstant;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructExpressionFromValue;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.constructLabelAssignment;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.unifyIdentifier;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
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
	 * Constructs initial declarations for global variables and the ULTIMATE.start procedure.
	 *
	 * This method initializes the global variables and constructs the ULTIMATE.start procedure that will be executed at
	 * the start of the program. It also constructs an aux#init procedure for global variable initialization.
	 *
	 * Using addFirst ensures that the initial declarations are at the beginning of the Boogie AST unit.
	 */
	private void constructInitialDeclarations() {
		final ArrayList<Statement> stmts = new ArrayList<>();
		final ArrayList<Specification> specs = new ArrayList<>();
		final ArrayList<Declaration> decls = new ArrayList<>();
		for (final String key : mGlobalVars.keySet()) {
			final Pair<Declaration, Statement> pair = mGlobalVars.get(key);
			if (pair == null) {
				mLogger.error("No pair found for global variable: " + key);
				continue;
			}
			decls.add(pair.getFirst());
			stmts.add(pair.getSecond());
			specs.add(constructSpecFromIdentifier(unifyIdentifier(key), (LlvmirLocation) pair.getSecond().getLoc()));
		}

		final String initIdentifier = "aux#init";
		mDeclarations.addFirst(constructInitialProcedure(mLocation, initIdentifier, new VariableDeclaration[] {},
				stmts.toArray(Statement[]::new), specs.toArray(Specification[]::new)));
		final CallStatement initCall =
				new CallStatement(mLocation, false, new VariableLHS[] {}, initIdentifier, new Expression[] {});

		VariableLHS[] lhsVars;
		VariableDeclaration[] varDecls;
		final String mainReturnType = getMainReturnType();
		if (mainReturnType.equals("void")) {
			lhsVars = new VariableLHS[] {};
			varDecls = new VariableDeclaration[] {};
		} else {
			final String tmpVarIdentifier = "aux#tmp";
			final VariableLHS varLhs = new VariableLHS(mLocation, tmpVarIdentifier);
			lhsVars = new VariableLHS[] { varLhs };
			varDecls = new VariableDeclaration[] {
					constructVarDecFromString(mainReturnType, tmpVarIdentifier, mLocation) };
		}
		final CallStatement mainCall = new CallStatement(mLocation, false, lhsVars, "#main", new Expression[] {});

		mDeclarations.addFirst(constructInitialProcedure(mLocation, "ULTIMATE.start", varDecls,
				new Statement[] { initCall, mainCall }, specs.toArray(Specification[]::new)));

		mDeclarations.addAll(0, decls);
	}

	/**
	 * Retrieves the return type of the #main procedure.
	 *
	 * This method searches for the #main procedure in the declarations and returns its return type as a String. If no
	 * such procedure is found, it throws an IllegalStateException.
	 *
	 * @return The return type of the #main procedure.
	 * @throws IllegalStateException
	 *             if no #main procedure is found in the declarations.
	 */
	private String getMainReturnType() throws IllegalStateException {
		final Procedure main = (Procedure) mDeclarations.stream()
				.filter(decl -> decl instanceof Procedure && ((Procedure) decl).getIdentifier().equals("#main"))
				.findFirst().orElseThrow(() -> new IllegalStateException("No #main declaration found"));
		final String retString = main.getOutParams().length > 0 ? main.getOutParams()[0].getType().toString() : "void";
		return retString.contains("int") ? "int" : retString.contains("bool") ? "bool" : "void";
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

		constructInitialDeclarations();
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
		final String funcName = unifyIdentifier(ctx.funcHeader().GlobalIdent().getText());
		final LLVMIRParser.TypeContext returnType = ctx.funcHeader().type();

		final LlvmirLocation location = constructLocation(ctx);

		final Body body = new Body(location, result.getFuncLocalVars().toArray(VariableDeclaration[]::new),
				result.getFuncBlock().toArray(Statement[]::new));
		final ArrayList<Attribute> attributes = new ArrayList<>();
		final ArrayList<String> typeParams = new ArrayList<>();
		final ArrayList<VarList> inParams = new ArrayList<>();
		final ArrayList<VarList> outParams = new ArrayList<>();

		for (final LLVMIRParser.ParamContext param : ctx.funcHeader().params().param()) {
			PrimitiveType paramType = null;
			if (param.type().intType().getText().equals("i1")) {
				paramType = new PrimitiveType(location, "bool");
			} else {
				paramType = new PrimitiveType(location, "int");
			}
			final VarList varList =
					new VarList(location, new String[] { unifyIdentifier(param.LocalIdent().getText()) }, paramType);
			inParams.add(varList);
		}

		if (returnType.getText().equals("void")) {
			// Nothing gets returned
		} else if (returnType.intType() != null) {
			PrimitiveType returnTypePrim = null;
			if (returnType.intType().getText().equals("i1")) {
				returnTypePrim = new PrimitiveType(location, "bool");
			} else {
				returnTypePrim = new PrimitiveType(location, "int");
			}
			final VarList retVarList = new VarList(location, new String[] { "ret" }, returnTypePrim);
			outParams.add(retVarList);
		} else {
			throw new AssertionError(
					"The support for return types other than void and integers is not implemented yet.");
		}

		final Procedure procedure = new Procedure(location, attributes.toArray(Attribute[]::new), funcName,
				typeParams.toArray(String[]::new), inParams.toArray(VarList[]::new), outParams.toArray(VarList[]::new),
				result.getFuncModifiedGlobalVars().toArray(Specification[]::new), body);

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
		} else if (instructionType.truncInst() != null) {
			handleTruncInst(result, instructionType, identifier, location);
		} else if (instructionType.extractValueInst() != null) {
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
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { structAccessExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.andInst() != null) {
			constructHavocStatementFromTypeValue(result, instructionType.andInst().typeValue(), location, identifier,
					"andInst");
		} else if (instructionType.orInst() != null) {
			constructHavocStatementFromTypeValue(result, instructionType.orInst().typeValue(), location, identifier,
					"orInst");
		} else if (instructionType.xorInst() != null) {
			constructHavocStatementFromTypeValue(result, instructionType.xorInst().typeValue(), location, identifier,
					"xorInst");
		} else if (instructionType.shlInst() != null) {
			constructHavocStatementFromTypeValue(result, instructionType.shlInst().typeValue(), location, identifier,
					"shlInst");
		} else if (instructionType.aShrInst() != null) {
			constructHavocStatementFromTypeValue(result, instructionType.aShrInst().typeValue(), location, identifier,
					"aShrInst");
		} else if (instructionType.lShrInst() != null) {
			constructHavocStatementFromTypeValue(result, instructionType.lShrInst().typeValue(), location, identifier,
					"lShrInst");
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