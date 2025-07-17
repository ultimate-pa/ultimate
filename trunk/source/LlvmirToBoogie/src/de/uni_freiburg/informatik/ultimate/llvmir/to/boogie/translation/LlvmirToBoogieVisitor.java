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

import java.util.ArrayList;
import java.util.Arrays;

import org.antlr.v4.runtime.tree.ParseTree;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRBaseVisitor;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;

public class LlvmirToBoogieVisitor extends LLVMIRBaseVisitor {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private Unit mResult;
	private final String mFilename;
	private LlvmirLocation mLocation;

	private final ArrayList<Declaration> mDeclarations = new ArrayList<>();

	public LlvmirToBoogieVisitor(final IUltimateServiceProvider services, final ILogger logger, final String filename) {
		assert services != null;
		mServices = services;
		mLogger = logger;
		mFilename = filename;
		mLocation = null;
		mLogger.info("Starting translation of LLVM IR to Boogie for file: " + mFilename);
	}

	public Unit getResult() {
		return mResult;
	}

	/**
	 * Unifies the identifier by ensuring it starts with a # character.
	 *
	 * This method is used to standardize the identifiers in the Boogie AST, as they are expected to start with #.
	 *
	 * @param identifier The original identifier from the LLVM IR parse tree.
	 * @return The unified identifier starting with #, or the original identifier if it is null or empty.
	 */
	private static String unifyIdentifier(final String identifier) {
		if (identifier == null || identifier.isEmpty()) {
			return identifier;
		}
		return "#" + identifier.substring(1);
	}

	/**
	 * Creates the initial declarations for the Boogie translation, specifically an #init procedure and a ULTIMATE.start
	 * procedure that calls #init and #main.
	 *
	 * The #init procedure is empty, while the ULTIMATE.start procedure initializes the program by calling both #init
	 * and #main.
	 */
	private void createInitialDeclarations() {
		final Body initBody = new Body(mLocation, new VariableDeclaration[] {}, new Statement[] {});
		final Procedure initProcedure = new Procedure(mLocation, new Attribute[] {}, "#init", new String[] {},
				new VarList[] {}, new VarList[] {}, new Specification[] {}, initBody);
		mDeclarations.add(initProcedure);
		final CallStatement initCall = new CallStatement(mLocation, false, new VariableLHS[] {}, "#init",
				new Expression[] {});

		final PrimitiveType intType = new PrimitiveType(mLocation, "int");
		final VarList varList = new VarList(mLocation, new String[] { "tmp" }, intType);
		final VariableDeclaration varDecl = new VariableDeclaration(mLocation, new Attribute[] {},
				new VarList[] { varList });
		final VariableLHS varLhs = new VariableLHS(mLocation, "tmp");
		final CallStatement mainCall = new CallStatement(mLocation, false, new VariableLHS[] { varLhs }, "#main",
				new Expression[] {});
		final Body startBody = new Body(mLocation, new VariableDeclaration[] { varDecl },
				new Statement[] { initCall, mainCall });
		final Procedure startProcedure = new Procedure(mLocation, new Attribute[] {}, "ULTIMATE.start", new String[] {},
				new VarList[] {}, new VarList[] {}, new Specification[] {}, startBody);
		mDeclarations.add(startProcedure);
	}

	/**
	 * Retrieves the #init procedure from the list of declarations.
	 *
	 * @return The #init procedure.
	 * @throws IllegalStateException if no #init procedure is found.
	 */
	private Procedure getInitProcedure() throws IllegalStateException {
		return (Procedure) mDeclarations.stream()
				.filter(decl -> decl instanceof Procedure && ((Procedure) decl).getIdentifier().equals("#init"))
				.findFirst().orElseThrow(() -> new IllegalStateException("No #init declaration found"));
	}

	/**
	 * Retrieves the ULTIMATE.start procedure from the list of declarations.
	 *
	 * @return The ULTIMATE.start procedure.
	 * @throws IllegalStateException if no ULTIMATE.start procedure is found.
	 */
	private Procedure getStartProcedure() throws IllegalStateException {
		return (Procedure) mDeclarations.stream().filter(
				decl -> decl instanceof Procedure && ((Procedure) decl).getIdentifier().equals("ULTIMATE.start"))
				.findFirst().orElseThrow(() -> new IllegalStateException("No ULTIMATE.start declaration found"));
	}

	/**
	 * Updates the specified procedure with a new assignment statement and modifies specification.
	 *
	 * This method removes the old procedure, updates its body with the new assignment, and adds a modifies
	 * specification for the variable being modified. The updated procedure is then added back to the list of
	 * declarations. If either assignment or modifiesSpec is null, only the non-null argument will be used to update the
	 * procedure; if both are null, the procedure will remain unchanged.
	 *
	 * @param procedure    The procedure to be updated.
	 * @param assignment   The assignment statement to be added to the procedure.
	 * @param modifiesSpec The modifies specification for the variable being modified.
	 * @throws IllegalArgumentException if the procedure is null.
	 */
	private void updateProcedure(final Procedure procedure, final AssignmentStatement assignment,
			final Specification modifiesSpec) throws IllegalArgumentException {
		if (procedure == null) {
			throw new IllegalArgumentException("Procedure cannot be null");
		}
		mDeclarations.remove(procedure);
		final ArrayList<Statement> newBlock = new ArrayList<>(Arrays.asList(procedure.getBody().getBlock()));
		if (assignment != null) {
			newBlock.add(assignment);
		}
		final ArrayList<Specification> newSpecs = new ArrayList<>(Arrays.asList(procedure.getSpecification()));
		if (modifiesSpec != null) {
			newSpecs.add(modifiesSpec);
		}

		final Body newBody = new Body(procedure.getBody().getLocation(), procedure.getBody().getLocalVars(),
				newBlock.toArray(new Statement[0]));
		final Procedure newProcedure = new Procedure(procedure.getLocation(), procedure.getAttributes(),
				procedure.getIdentifier(), procedure.getTypeParams(), procedure.getInParams(), procedure.getOutParams(),
				newSpecs.toArray(new Specification[0]), newBody);

		mDeclarations.add(newProcedure);
	}

	/**
	 * Creates a variable declaration with a primitive type.
	 *
	 * This method is used to create variable declarations for primitive types like integers, booleans, etc.
	 *
	 * @param type       The type of the variable (e.g., "int", "bool").
	 * @param identifier The identifier for the variable.
	 * @param location   The location in the source code where this variable is declared.
	 * @return A VariableDeclaration object representing the variable declaration.
	 */
	private static VariableDeclaration createVarDecWithPrimType(final String type, final String identifier,
			final LlvmirLocation location) {
		final PrimitiveType primType = new PrimitiveType(location, type);
		final VarList varList = new VarList(location, new String[] { unifyIdentifier(identifier) }, primType);
		final VariableDeclaration varDecl = new VariableDeclaration(location, new Attribute[] {},
				new VarList[] { varList });

		return varDecl;
	}

	/**
	 * Converts a value context from the LLVM IR parse tree into a Boogie expression.
	 *
	 * This method handles both local identifiers and constant values, converting them into the appropriate Boogie
	 * expressions (IdentifierExpression or IntegerLiteral).
	 *
	 * @param valueContext The value context from the LLVM IR parse tree.
	 * @param location     The location in the source code where this value is used.
	 * @return An Expression object representing the value.
	 * @throws AssertionError if the value type is not supported.
	 */
	private static Expression getExpressionFromValue(final LLVMIRParser.ValueContext valueContext,
			final LlvmirLocation location) throws AssertionError {
		if (valueContext.LocalIdent() != null) {
			final String leftOperandName = valueContext.LocalIdent().getText();
			return new IdentifierExpression(location, unifyIdentifier(leftOperandName));
		} else if (valueContext.constant() != null) {
			if (valueContext.constant().intConst() != null) {
				final int constValue = Integer.parseInt(valueContext.constant().intConst().getText());
				if (constValue >= 0) {
					return new IntegerLiteral(location, Integer.toString(constValue));
				}
				final IntegerLiteral absValue = new IntegerLiteral(location, Integer.toString(Math.abs(constValue)));
				return new UnaryExpression(location, UnaryExpression.Operator.ARITHNEGATIVE, absValue);
			} else if (valueContext.constant().boolConst() != null) {
				final String boolValue = valueContext.constant().boolConst().getText();
				return new IdentifierExpression(location, boolValue);
			}
			// TODO: Support for other constant operand types
			throw new AssertionError(
					"The support for iCmp instructions with constant operands other than integers and booleans is not implemented yet.");
		} else {
			// TODO: Support for other left operand types
			throw new AssertionError(
					"The support for iCmp instructions with operands other than constants or local identifiers is not implemented yet.");
		}
	}

	@Override
	public Void visitCompilationUnit(final LLVMIRParser.CompilationUnitContext ctx) {
		mLocation = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());
		createInitialDeclarations();

		visitChildren(ctx);

		mResult = new Unit(mLocation, mDeclarations.toArray(Declaration[]::new));
		return null;
	}

	/**
	 * Handles the visit event for a function definition in the LLVM IR parse tree.
	 *
	 * This method translates the parsed LLVM IR function into a Boogie procedure, including its body, parameters, and
	 * return type. Currently, only `void` and integer return types are supported.
	 *
	 * @param ctx The parse tree context for the function definition.
	 * @throws AssertionError if the return type is not supported.
	 */
	@Override
	public Void visitFuncDef(final LLVMIRParser.FuncDefContext ctx) throws AssertionError {
		final FunctionBody body = new FunctionBody();
		for (final ParseTree child : ctx.children) {
			final FunctionBody childBody = (FunctionBody) child.accept(this);
			if (childBody != null) {
				body.merge(childBody);
			}
		}

		final String funcName = unifyIdentifier(ctx.funcHeader().GlobalIdent().getText());
		final LLVMIRParser.TypeContext returnType = ctx.funcHeader().type();

		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		final Body funcBody = new Body(location, body.getFuncLocalVars().toArray(VariableDeclaration[]::new),
				body.getFuncBlock().toArray(Statement[]::new));
		final ArrayList<Attribute> attributes = new ArrayList<>();
		final ArrayList<String> typeParams = new ArrayList<>();
		final ArrayList<VarList> inParams = new ArrayList<>();
		final ArrayList<VarList> outParams = new ArrayList<>();
		final ArrayList<Specification> spec = new ArrayList<>();

		if (returnType.getText().equals("void")) {
			// Nothing gets returned
		} else if (returnType.intType() != null) {
			final PrimitiveType intType = new PrimitiveType(location, "int");
			final VarList retVarList = new VarList(location, new String[] { "ret" }, intType);
			outParams.add(retVarList);
		} else {
			// TODO: Support for other types
			throw new AssertionError(
					"The support for return types other than void and integers is not implemented yet.");
		}

		final Procedure procedure = new Procedure(location, attributes.toArray(Attribute[]::new), funcName,
				typeParams.toArray(String[]::new), inParams.toArray(VarList[]::new), outParams.toArray(VarList[]::new),
				spec.toArray(Specification[]::new), funcBody);
		mDeclarations.add(procedure);

		return null;
	}

	/**
	 * Handles the visit event for a function body in the LLVM IR parse tree.
	 *
	 * This method processes the children of the function body context and merges their results into a single
	 * FunctionBody object.
	 *
	 * @param ctx The parse tree context for the function body.
	 * @return A FunctionBody object containing the merged results of the children.
	 */
	@Override
	public FunctionBody visitFuncBody(final LLVMIRParser.FuncBodyContext ctx) {
		final FunctionBody body = new FunctionBody();
		for (final ParseTree child : ctx.children) {
			final FunctionBody childBody = (FunctionBody) child.accept(this);
			if (childBody != null) {
				body.merge(childBody);
			}
		}
		return body;
	}

	/**
	 * Handles the visit event for a function body in the LLVM IR parse tree.
	 *
	 * This method processes the children of the function body context and merges their results into a single
	 * FunctionBody object.
	 *
	 * @param ctx The parse tree context for the function body.
	 * @return A FunctionBody object containing the merged results of the children.
	 */
	@Override
	public FunctionBody visitBasicBlock(final LLVMIRParser.BasicBlockContext ctx) {
		final FunctionBody body = new FunctionBody();
		for (final ParseTree child : ctx.children) {
			final FunctionBody childBody = (FunctionBody) child.accept(this);
			if (childBody != null) {
				body.merge(childBody);
			}
		}
		return body;
	}

	/**
	 * Handles the visit event for a return terminator in the LLVM IR parse tree.
	 *
	 * Currently, it only supports integer return types.
	 *
	 * @param ctx The parse tree context for the return terminator.
	 * @throws AssertionError if the return type is not supported.
	 */
	@Override
	public FunctionBody visitRetTerm(final LLVMIRParser.RetTermContext ctx) {
		final FunctionBody body = new FunctionBody();
		final LLVMIRParser.ConcreteTypeContext returnType = ctx.concreteType();
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		if (returnType.intType() != null) {
			final VariableLHS returnVar = new VariableLHS(location, "ret");
			final AssignmentStatement assignmentStmt = new AssignmentStatement(location,
					new LeftHandSide[] { returnVar },
					new Expression[] { getExpressionFromValue(ctx.value(), location) });
			final ReturnStatement returnStmt = new ReturnStatement(location);
			body.addFuncBlocks(Arrays.asList(assignmentStmt, returnStmt));
		} else {
			// TODO: Support for other types
			throw new AssertionError("The support for return types other than integers is not implemented yet.");
		}

		return body;
	}

	/**
	 * Handles the visit event for a global variable definition in the LLVM IR parse tree.
	 *
	 * This method translates the global variable definition into a Boogie variable declaration and updates the `#init`
	 * procedure with an assignment statement to initialize the variable.
	 *
	 * @param ctx The parse tree context for the global variable definition.
	 * @throws AssertionError if the type of the global variable is not supported.
	 */
	@Override
	public Void visitGlobalDef(final LLVMIRParser.GlobalDefContext ctx) {
		final LLVMIRParser.TypeContext type = ctx.type();
		final String identifier = ctx.GlobalIdent().getText();
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		if (type.intType() != null) {
			mDeclarations.add(createVarDecWithPrimType("int", identifier, location));

			final VariableLHS varLhs = new VariableLHS(location, unifyIdentifier(identifier));
			final IntegerLiteral initValue = new IntegerLiteral(location, ctx.constant().intConst().getText());
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { initValue });

			final Specification modifiesSpec = new ModifiesSpecification(mLocation, false,
					new VariableLHS[] { varLhs });

			updateProcedure(getInitProcedure(), assignment, modifiesSpec);
			updateProcedure(getStartProcedure(), null, modifiesSpec);
		} else {
			// TODO: Support for other types
			throw new AssertionError("The support for types other than integers is not implemented yet.");
		}

		return null;
	}

	/**
	 * Handles the visit event for a local variable definition in the LLVM IR parse tree.
	 *
	 * This method translates the local variable definition into a Boogie variable declaration and initializes it based
	 * on the type of instruction (load or iCmp). Currently, it supports load instructions for integers and iCmp
	 * instructions for equality checks.
	 *
	 * @param ctx The parse tree context for the local variable definition.
	 * @throws AssertionError if the instruction type is not supported.
	 */
	@Override
	public FunctionBody visitLocalDefInst(final LLVMIRParser.LocalDefInstContext ctx) {
		final FunctionBody body = new FunctionBody();
		final String identifier = ctx.LocalIdent().getText();
		final LLVMIRParser.ValueInstructionContext instructionType = ctx.valueInstruction();
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		if (instructionType.loadInst() != null) {
			final LLVMIRParser.TypeContext variableType = instructionType.loadInst().type();
			if (variableType.intType() != null) {
				body.addFuncLocalVar(createVarDecWithPrimType("int", identifier, location));
				final VariableLHS varLhs = new VariableLHS(location, unifyIdentifier(identifier));
				final String nameOfGlobalVar = instructionType.loadInst().typeValue().value().constant().GlobalIdent()
						.getText();
				final IdentifierExpression globalVarExpr = new IdentifierExpression(location,
						unifyIdentifier(nameOfGlobalVar));
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { globalVarExpr });
				body.addFuncBlock(assignment);
				// TODO
			} else {
				// TODO: Support for other types
				throw new AssertionError(
						"The support for types other than integers in load instructions is not implemented yet.");
			}
		} else if (instructionType.iCmpInst() != null) {
			body.addFuncLocalVar(createVarDecWithPrimType("bool", identifier, location));
			Expression leftExpr = null;
			Expression rightExpr = null;
			Operator operator = null;
			final String OperatorValue = instructionType.iCmpInst().iPred().getText();
			if (OperatorValue.equals("eq")) {
				operator = Operator.COMPEQ;
			} else {
				// TODO: Support for other iCmp operators
				throw new AssertionError("The support for iCmp operators other than eq is not implemented yet.");
			}

			final LLVMIRParser.ValueContext leftOperandType = instructionType.iCmpInst().typeValue().value();
			leftExpr = getExpressionFromValue(leftOperandType, location);

			final LLVMIRParser.ValueContext rightOperandType = instructionType.iCmpInst().value();
			rightExpr = getExpressionFromValue(rightOperandType, location);

			final VariableLHS varLhs = new VariableLHS(null, unifyIdentifier(identifier));
			final BinaryExpression binaryExpr = new BinaryExpression(location, operator, leftExpr, rightExpr);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { binaryExpr });
			body.addFuncBlock(assignment);
		} else {
			// TODO: Support for other instructions
			throw new AssertionError("The support for instructions other than load is not implemented yet.");
		}

		return body;
	}
}
