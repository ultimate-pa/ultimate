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
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRBaseListener;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;

public class LlvmirToBoogieListener extends LLVMIRBaseListener {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private Unit mResult;
	private final String mFilename;

	// Temporary storage for function-local variables and statements
	private ArrayList<VariableDeclaration> mFuncLocalVars = new ArrayList<>();
	private ArrayList<Statement> mFuncBlock = new ArrayList<>();
	// Storage for the declarations that will be part of the final Boogie Unit
	private final ArrayList<Declaration> mDeclarations = new ArrayList<>();

	public LlvmirToBoogieListener(final IUltimateServiceProvider services, final ILogger logger,
			final String filename) {
		assert services != null;
		mServices = services;
		mLogger = logger;
		mFilename = filename;
		mLogger.info("Starting translation of LLVM IR to Boogie for file: " + mFilename);
		createInitialDeclarations();
	}

	public Unit getResult() {
		return mResult;
	}

	/**
	 * Creates the initial declarations for the Boogie translation, specifically an `#init` procedure and a
	 * `ULTIMATE.start` procedure that calls `#init` and `#main`.
	 *
	 * The `#init` procedure is empty, while the `ULTIMATE.start` procedure initializes the program by calling both
	 * `#init` and `#main`.
	 */
	private void createInitialDeclarations() {
		final Body initBody = new Body(
				new DefaultLocation("Location_of_LlvmirToBoogie_initBody_in_createInitialDeclarations", -1, -1, -1, -1),
				new VariableDeclaration[] {}, new Statement[] {});
		final Procedure initProcedure = new Procedure(
				new DefaultLocation("Location_of_LlvmirToBoogie_initProcedure_in_createInitialDeclarations", -1, -1, -1,
						-1),
				new Attribute[] {}, "#init", new String[] {}, new VarList[] {}, new VarList[] {},
				new Specification[] {}, initBody);
		mDeclarations.add(initProcedure);
		final CallStatement initCall = new CallStatement(
				new DefaultLocation("Location_of_LlvmirToBoogie_initCall_in_createInitialDeclarations", -1, -1, -1, -1),
				false, new VariableLHS[] {}, "#init", new Expression[] {});

		final PrimitiveType intType = new PrimitiveType(
				new DefaultLocation("Location_of_LlvmirToBoogie_intType_in_createInitialDeclarations", -1, -1, -1, -1),
				"int");
		final VarList varList = new VarList(
				new DefaultLocation("Location_of_LlvmirToBoogie_varList_in_createInitialDeclarations", -1, -1, -1, -1),
				new String[] { "tmp" }, intType);
		final VariableDeclaration varDecl = new VariableDeclaration(
				new DefaultLocation("Location_of_LlvmirToBoogie_varDecl_in_createInitialDeclarations", -1, -1, -1, -1),
				new Attribute[] {}, new VarList[] { varList });
		final VariableLHS varLhs = new VariableLHS(
				new DefaultLocation("Location_of_LlvmirToBoogie_varLhs_in_createInitialDeclarations", -1, -1, -1, -1),
				"tmp");
		final CallStatement mainCall = new CallStatement(
				new DefaultLocation("Location_of_LlvmirToBoogie_mainCall_in_createInitialDeclarations", -1, -1, -1, -1),
				false, new VariableLHS[] { varLhs }, "#main", new Expression[] {});
		final Body startBody = new Body(
				new DefaultLocation("Location_of_LlvmirToBoogie_startBody_in_createInitialDeclarations", -1, -1, -1,
						-1),
				new VariableDeclaration[] { varDecl }, new Statement[] { initCall, mainCall });
		final Procedure startProcedure = new Procedure(
				new DefaultLocation("Location_of_LlvmirToBoogie_startProcedure_in_createInitialDeclarations", -1, -1,
						-1, -1),
				new Attribute[] {}, "ULTIMATE.start", new String[] {}, new VarList[] {}, new VarList[] {},
				new Specification[] {}, startBody);
		mDeclarations.add(startProcedure);
	}

	/**
	 * Retrieves the `#init` procedure from the list of declarations.
	 *
	 * @return The `#init` procedure.
	 * @throws IllegalStateException if no `#init` procedure is found.
	 */
	private Procedure getInitProcedure() throws IllegalStateException {
		return (Procedure) mDeclarations.stream()
				.filter(decl -> decl instanceof Procedure && ((Procedure) decl).getIdentifier().equals("#init"))
				.findFirst().orElseThrow(() -> new IllegalStateException("No #init declaration found"));
	}

	/**
	 * Retrieves the `ULTIMATE.start` procedure from the list of declarations.
	 *
	 * @return The `ULTIMATE.start` procedure.
	 * @throws IllegalStateException if no `ULTIMATE.start` procedure is found.
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
	 * Handles the exit event for the compilation unit in the LLVM IR parse tree.
	 *
	 * This method creates the initial procedures required for the Boogie translation, specifically an `#init` procedure
	 * and a `ULTIMATE.start` procedure that calls `#init` and `#main`. These procedures are added to the list of
	 * declarations, and the resulting Boogie `Unit` is constructed and stored.
	 *
	 * @param ctx The parse tree context for the compilation unit.
	 */
	@Override
	public void exitCompilationUnit(final LLVMIRParser.CompilationUnitContext ctx) {
		final DefaultLocation location = new DefaultLocation("Location_of_LlvmirToBoogie_Result", -1, -1, -1, -1);
		mResult = new Unit(location, mDeclarations.toArray(Declaration[]::new));
	}

	/**
	 * Handles the exit event for a function definition in the LLVM IR parse tree.
	 *
	 * This method translates the parsed LLVM IR function into a Boogie procedure, including its body, parameters, and
	 * return type. Currently, only `void` and integer return types are supported.
	 *
	 * @param ctx The parse tree context for the function definition.
	 * @throws AssertionError if the return type is not supported.
	 */
	@Override
	public void exitFuncDef(final LLVMIRParser.FuncDefContext ctx) throws AssertionError {
		final String funcName = unifyIdentifier(ctx.funcHeader().GlobalIdent().getText());
		final LLVMIRParser.TypeContext returnType = ctx.funcHeader().type();
		final Body funcBody = new Body(new DefaultLocation(), mFuncLocalVars.toArray(VariableDeclaration[]::new),
				mFuncBlock.toArray(Statement[]::new));
		final ArrayList<Attribute> attributes = new ArrayList<>();
		final ArrayList<String> typeParams = new ArrayList<>();
		final ArrayList<VarList> inParams = new ArrayList<>();
		final ArrayList<VarList> outParams = new ArrayList<>();
		final ArrayList<Specification> spec = new ArrayList<>();

		if (returnType.getText().equals("void")) {
			// Nothing gets returned
		} else if (returnType.intType() != null) {
			final PrimitiveType intType = new PrimitiveType(
					new DefaultLocation("Location_of_LlvmirToBoogie_intType_in_exitFuncDef", -1, -1, -1, -1), "int");
			final VarList retVarList = new VarList(
					new DefaultLocation("Location_of_LlvmirToBoogie_retVarList_in_exitFuncDef", -1, -1, -1, -1),
					new String[] { "ret" }, intType);
			outParams.add(retVarList);
		} else {
			// TODO: Support for other types
			throw new AssertionError(
					"The support for return types other than void and integers is not implemented yet.");
		}

		final Procedure procedure = new Procedure(
				new DefaultLocation("Location_of_LlvmirToBoogie_procedure_in_exitFuncDef", -1, -1, -1, -1),
				attributes.toArray(Attribute[]::new), funcName, typeParams.toArray(String[]::new),
				inParams.toArray(VarList[]::new), outParams.toArray(VarList[]::new), spec.toArray(Specification[]::new),
				funcBody);
		mDeclarations.add(procedure);

		mFuncBlock = new ArrayList<>();
		mFuncLocalVars = new ArrayList<>();
	}

	/**
	 * Unifies the identifier by ensuring it starts with a `#` character.
	 *
	 * This method is used to standardize the identifiers in the Boogie AST, as they are expected to start with `#`.
	 *
	 * @param identifier The original identifier from the LLVM IR parse tree.
	 * @return The unified identifier starting with `#`, or the original identifier if it is null or empty.
	 */
	private static String unifyIdentifier(final String identifier) {
		if (identifier == null || identifier.isEmpty()) {
			return identifier;
		}
		return "#" + identifier.substring(1);
	}

	/**
	 * Handles the exit event for a return terminator in the LLVM IR parse tree.
	 *
	 * Currently, it only supports integer return types.
	 *
	 * @param ctx The parse tree context for the return terminator.
	 * @throws AssertionError if the return type is not supported.
	 */
	@Override
	public void exitRetTerm(final LLVMIRParser.RetTermContext ctx) throws AssertionError {
		final LLVMIRParser.ConcreteTypeContext returnType = ctx.concreteType();
		if (returnType.intType() != null) {
			final String returnValue = ctx.value().constant().intConst().getText();
			final IntegerLiteral returnLiteral = new IntegerLiteral(
					new DefaultLocation("Location_of_LlvmirToBoogie_returnLiteral_in_exitRetTerm", -1, -1, -1, -1),
					returnValue);
			final VariableLHS returnVar = new VariableLHS(
					new DefaultLocation("Location_of_LlvmirToBoogie_returnVar_in_exitRetTerm", -1, -1, -1, -1), "ret");
			final AssignmentStatement assignmentStmt = new AssignmentStatement(
					new DefaultLocation("Location_of_LlvmirToBoogie_assignmentStmt_in_exitRetTerm", -1, -1, -1, -1),
					new LeftHandSide[] { returnVar }, new Expression[] { returnLiteral });
			final ReturnStatement returnStmt = new ReturnStatement(
					new DefaultLocation("Location_of_LlvmirToBoogie_returnStmt_in_exitRetTerm", -1, -1, -1, -1));
			mFuncBlock.add(assignmentStmt);
			mFuncBlock.add(returnStmt);
		} else {
			// TODO: Support for other types
			throw new AssertionError("The support for return types other than integers is not implemented yet.");
		}
	}

	/**
	 * Handles the exit event for a global variable definition in the LLVM IR parse tree.
	 *
	 * This method translates the global variable definition into a Boogie variable declaration and updates the `#init`
	 * procedure with an assignment statement to initialize the variable.
	 *
	 * @param ctx The parse tree context for the global variable definition.
	 * @throws AssertionError if the type of the global variable is not supported.
	 */
	@Override
	public void exitGlobalDef(final LLVMIRParser.GlobalDefContext ctx) throws AssertionError {
		final LLVMIRParser.TypeContext type = ctx.type();
		final String identifier = ctx.GlobalIdent().getText();
		if (type.intType() != null) {
			final PrimitiveType intType = new PrimitiveType(
					new DefaultLocation("Location_of_LlvmirToBoogie_intType_in_exitGlobalDef", -1, -1, -1, -1), "int");
			final VarList varList = new VarList(
					new DefaultLocation("Location_of_LlvmirToBoogie_varList_in_exitGlobalDef", -1, -1, -1, -1),
					new String[] { unifyIdentifier(identifier) }, intType);
			final VariableDeclaration varDecl = new VariableDeclaration(
					new DefaultLocation("Location_of_LlvmirToBoogie_varDecl_in_exitGlobalDef", -1, -1, -1, -1),
					new Attribute[] {}, new VarList[] { varList });
			mDeclarations.add(varDecl);

			final VariableLHS varLhs = new VariableLHS(
					new DefaultLocation("Location_of_LlvmirToBoogie_varLhs_in_exitGlobalDef", -1, -1, -1, -1),
					unifyIdentifier(identifier));
			final IntegerLiteral initValue = new IntegerLiteral(
					new DefaultLocation("Location_of_LlvmirToBoogie_initValue_in_exitGlobalDef", -1, -1, -1, -1),
					ctx.constant().intConst().getText());
			final AssignmentStatement assignment = new AssignmentStatement(
					new DefaultLocation("Location_of_LlvmirToBoogie_assignment_in_exitGlobalDef", -1, -1, -1, -1),
					new LeftHandSide[] { varLhs }, new Expression[] { initValue });

			final Specification modifiesSpec = new ModifiesSpecification(
					new DefaultLocation("Location_of_LlvmirToBoogie_modifiesSpec_in_exitGlobalDef", -1, -1, -1, -1),
					false, new VariableLHS[] { varLhs });

			updateProcedure(getInitProcedure(), assignment, modifiesSpec);
			updateProcedure(getStartProcedure(), null, modifiesSpec);
		} else {
			// TODO: Support for other types
			throw new AssertionError("The support for types other than integers is not implemented yet.");
		}
	}

	/**
	 * Handles the exit event for a local variable definition in the LLVM IR parse tree.
	 *
	 * This method translates the local variable definition into a Boogie variable declaration and initializes it based
	 * on the type of instruction (load or iCmp). Currently, it supports load instructions for integers and iCmp
	 * instructions for equality checks.
	 *
	 * @param ctx The parse tree context for the local variable definition.
	 * @throws AssertionError if the instruction type is not supported.
	 */
	@Override
	public void exitLocalDefInst(final LLVMIRParser.LocalDefInstContext ctx) throws AssertionError {
		final String identifier = ctx.LocalIdent().getText();
		final LLVMIRParser.ValueInstructionContext instructionType = ctx.valueInstruction();
		if (instructionType.loadInst() != null) {
			final LLVMIRParser.TypeContext variableType = instructionType.loadInst().type();
			if (variableType.intType() != null) {
				final PrimitiveType intType = new PrimitiveType(
						new DefaultLocation("Location_of_LlvmirToBoogie_intType_in_exitLocalDefInst", -1, -1, -1, -1),
						"int");
				final VarList varList = new VarList(
						new DefaultLocation("Location_of_LlvmirToBoogie_int_varList_in_exitLocalDefInst", -1, -1, -1,
								-1),
						new String[] { unifyIdentifier(identifier) }, intType);
				final VariableDeclaration varDecl = new VariableDeclaration(
						new DefaultLocation("Location_of_LlvmirToBoogie_int_varDecl_in_exitLocalDefInst", -1, -1, -1,
								-1),
						new Attribute[] {}, new VarList[] { varList });
				mFuncLocalVars.add(varDecl);
				final VariableLHS varLhs = new VariableLHS(
						new DefaultLocation("Location_of_LlvmirToBoogie_varLhs_in_exitLocalDefInst", -1, -1, -1, -1),
						unifyIdentifier(identifier));
				final String nameOfGlobalVar = instructionType.loadInst().typeValue().value().constant().GlobalIdent()
						.getText();
				final IdentifierExpression globalVarExpr = new IdentifierExpression(
						new DefaultLocation("Location_of_LlvmirToBoogie_globalVarExpr_in_exitLocalDefInst", -1, -1, -1,
								-1),
						unifyIdentifier(nameOfGlobalVar));
				final AssignmentStatement assignment = new AssignmentStatement(
						new DefaultLocation("Location_of_LlvmirToBoogie_assignment_in_exitLocalDefInst", -1, -1, -1,
								-1),
						new LeftHandSide[] { varLhs }, new Expression[] { globalVarExpr });
				mFuncBlock.add(assignment);
				// TODO
			} else {
				// TODO: Support for other types
				throw new AssertionError(
						"The support for types other than integers in load instructions is not implemented yet.");
			}
		} else if (instructionType.iCmpInst() != null) {
			final PrimitiveType boolType = new PrimitiveType(
					new DefaultLocation("Location_of_LlvmirToBoogie_boolType_in_exitLocalDefInst", -1, -1, -1, -1),
					"bool");
			final VarList varList = new VarList(
					new DefaultLocation("Location_of_LlvmirToBoogie_bool_varList_in_exitLocalDefInst", -1, -1, -1, -1),
					new String[] { unifyIdentifier(identifier) }, boolType);
			final VariableDeclaration varDecl = new VariableDeclaration(
					new DefaultLocation("Location_of_LlvmirToBoogie_bool_varDecl_in_exitLocalDefInst", -1, -1, -1, -1),
					new Attribute[] {}, new VarList[] { varList });
			mFuncLocalVars.add(varDecl);
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
			if (leftOperandType.constant() != null) {
				if (leftOperandType.constant().intConst() != null) {
					final int constValue = Integer.parseInt(leftOperandType.constant().intConst().getText());
					final IntegerLiteral leftOperand = new IntegerLiteral(
							new DefaultLocation("Location_of_LlvmirToBoogie_leftOperand1_in_exitLocalDefInst", -1, -1,
									-1, -1),
							Integer.toString(constValue));
					leftExpr = leftOperand;
				} else {
					// TODO: Support for other constant operand types
					throw new AssertionError(
							"The support for iCmp instructions with constant operands other than integers is not implemented yet.");
				}
			} else if (leftOperandType.LocalIdent() != null) {
				final String leftOperandName = leftOperandType.LocalIdent().getText();
				final IdentifierExpression leftOperand = new IdentifierExpression(
						new DefaultLocation("Location_of_LlvmirToBoogie_leftOperand2_in_exitLocalDefInst", -1, -1, -1,
								-1),
						unifyIdentifier(leftOperandName));
				leftExpr = leftOperand;
			} else {
				// TODO: Support for other left operand types
				throw new AssertionError(
						"The support for iCmp instructions with operands other than constants or local identifiers is not implemented yet.");
			}

			final LLVMIRParser.ValueContext rightOperandType = instructionType.iCmpInst().value();
			if (rightOperandType.constant() != null) {
				if (rightOperandType.constant().intConst() != null) {
					final int constValue = Integer.parseInt(rightOperandType.constant().intConst().getText());
					final IntegerLiteral rightOperand = new IntegerLiteral(
							new DefaultLocation("Location_of_LlvmirToBoogie_rightOperand1_in_exitLocalDefInst", -1, -1,
									-1, -1),
							Integer.toString(constValue));
					rightExpr = rightOperand;
				} else {
					// TODO: Support for other constant operand types
					throw new AssertionError(
							"The support for iCmp instructions with constant operands other than integers is not implemented yet.");
				}
			} else if (rightOperandType.LocalIdent() != null) {
				final String rightOperandName = rightOperandType.LocalIdent().getText();
				final IdentifierExpression rightOperand = new IdentifierExpression(
						new DefaultLocation("Location_of_LlvmirToBoogie_rightOperand2_in_exitLocalDefInst", -1, -1, -1,
								-1),
						unifyIdentifier(rightOperandName));
				rightExpr = rightOperand;
			} else {
				// TODO: Support for other right operand types
				throw new AssertionError(
						"The support for iCmp instructions with operands other than constants or local identifiers is not implemented yet.");
			}

			final VariableLHS varLhs = new VariableLHS(
					new DefaultLocation("Location_of_LlvmirToBoogie_varLhs_end_in_exitLocalDefInst", -1, -1, -1, -1),
					unifyIdentifier(identifier));
			final BinaryExpression binaryExpr = new BinaryExpression(
					new DefaultLocation("Location_of_LlvmirToBoogie_binaryExpr_in_exitLocalDefInst", -1, -1, -1, -1),
					operator, leftExpr, rightExpr);
			final AssignmentStatement assignment = new AssignmentStatement(
					new DefaultLocation("Location_of_LlvmirToBoogie_assignment_end_in_exitLocalDefInst", -1, -1, -1,
							-1),
					new LeftHandSide[] { varLhs }, new Expression[] { binaryExpr });
			mFuncBlock.add(assignment);
		} else {
			// TODO: Support for other instructions
			throw new AssertionError("The support for instructions other than load is not implemented yet.");
		}
	}
}
