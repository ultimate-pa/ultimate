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
import java.util.List;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
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
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRBaseVisitor;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;

public class LlvmirToBoogieVisitor extends LLVMIRBaseVisitor<FunctionBody> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private Unit mResult;
	private final String mFilename;
	private LlvmirLocation mLocation;
	private final String mLabelIdentifier = "#label";
	private final static String mUndefIdentifier = "#undef";

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
		String result = identifier;
		result = result.replace(":", "");
		final char firstChar = result.charAt(0);
		if (Character.isLetterOrDigit(firstChar)) {
			return "#" + result;
		}
		return "#" + result.substring(1);
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
		final VarList varList = new VarList(mLocation, new String[] { "#tmp" }, intType);
		final VariableDeclaration varDecl = new VariableDeclaration(mLocation, new Attribute[] {},
				new VarList[] { varList });
		final VariableLHS varLhs = new VariableLHS(mLocation, "#tmp");
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
				return new BooleanLiteral(location, valueContext.constant().boolConst().getText().equals("true"));
			} else if (valueContext.constant().undefConst() != null) {
				return new IdentifierExpression(location, mUndefIdentifier);
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

	/**
	 * Retrieves the index of a label from the function body based on the provided identifier.
	 *
	 * This method traverses the parent hierarchy of the given context to find the function body and then searches for
	 * the label with the specified identifier within that function body.
	 *
	 * @param ctx           The context from which to start searching for the function body.
	 * @param incIdentifier The identifier of the label to find.
	 * @return The index of the label in the function body.
	 * @throws IllegalArgumentException if the context or identifier is null or empty, or if no label is found.
	 */
	private static int getLabelIndexFromFuncBody(final ParserRuleContext ctx, final String incIdentifier)
			throws IllegalArgumentException {
		if (ctx == null || incIdentifier == null || incIdentifier.isEmpty()) {
			throw new IllegalArgumentException("Context and identifier must not be null or empty");
		}
		LLVMIRParser.FuncBodyContext funcBodyCtx = null;
		ParserRuleContext tmpCtx = ctx;
		while (funcBodyCtx == null) {
			if (tmpCtx.getParent() instanceof LLVMIRParser.FuncBodyContext) {
				funcBodyCtx = (LLVMIRParser.FuncBodyContext) tmpCtx.getParent();
			} else if (tmpCtx.getParent() != null) {
				tmpCtx = tmpCtx.getParent();
			} else {
				throw new IllegalArgumentException("No FuncBodyContext found in the parent hierarchy");
			}
		}
		int labelIndex = -1;
		final List<LLVMIRParser.BasicBlockContext> basicBlocks = funcBodyCtx.basicBlock();
		for (final LLVMIRParser.BasicBlockContext block : basicBlocks) {
			if (block.LabelIdent() != null && unifyIdentifier(block.LabelIdent().getText()).equals(incIdentifier)) {
				labelIndex = basicBlocks.indexOf(block);
				break;
			}
		}
		if (labelIndex == -1) {
			throw new IllegalArgumentException("No label found for identifier: " + incIdentifier);
		}
		return labelIndex;
	}

	/**
	 * Creates an assignment statement to assign a label index to the label variable.
	 *
	 * This method constructs an assignment statement that assigns the specified label index to the label variable
	 * identified by `mLabelIdentifier`.
	 *
	 * @param location   The location in the source code where this assignment occurs.
	 * @param labelIndex The index of the label to be assigned.
	 * @return An AssignmentStatement object representing the assignment.
	 */
	private AssignmentStatement createLabelAssignment(final LlvmirLocation location, final int labelIndex) {
		final IntegerLiteral labelIndexLiteral = new IntegerLiteral(location, Integer.toString(labelIndex));
		final VariableLHS labelVar = new VariableLHS(location, mLabelIdentifier);
		return new AssignmentStatement(location, new LeftHandSide[] { labelVar },
				new Expression[] { labelIndexLiteral });
	}

	/**
	 * Creates an arithmetic assignment statement for a given identifier, left and right values, and an operator.
	 *
	 * This method constructs an assignment statement that performs an arithmetic operation (addition, subtraction,
	 * multiplication, or division) on the left and right values and assigns the result to the specified identifier.
	 *
	 * @param location   The location in the source code where this assignment occurs.
	 * @param identifier The identifier to which the result of the arithmetic operation will be assigned.
	 * @param leftValue  The left operand value context from the LLVM IR parse tree.
	 * @param rightValue The right operand value context from the LLVM IR parse tree.
	 * @param operator   The operator to be used for the arithmetic operation.
	 * @return An AssignmentStatement object representing the arithmetic assignment.
	 */
	private static AssignmentStatement createArithmeticAssignment(final LlvmirLocation location,
			final String identifier, final LLVMIRParser.ValueContext leftValue,
			final LLVMIRParser.ValueContext rightValue, final Operator operator) {
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final Expression leftExpr = getExpressionFromValue(leftValue, location);
		final Expression rightExpr = getExpressionFromValue(rightValue, location);
		final BinaryExpression binaryExpr = new BinaryExpression(location, operator, leftExpr, rightExpr);
		return new AssignmentStatement(location, new LeftHandSide[] { varLhs }, new Expression[] { binaryExpr });
	}

	/**
	 * Converts a string representation of a comparison operator to its corresponding Boogie operator.
	 *
	 * This method maps the LLVM IR comparison operators (like "eq", "ne", "sle", etc.) to their Boogie equivalents
	 * (like COMPEQ, COMPNEQ, COMPLEQ, etc.).
	 *
	 * @param operatorValue The string representation of the comparison operator.
	 * @return The corresponding Boogie Operator.
	 * @throws AssertionError if the operator is not supported.
	 */
	private static Operator getCompOperatorFromOperatorValue(final String operatorValue) {
		switch (operatorValue) {
		case "eq":
			return Operator.COMPEQ;
		case "ne":
			return Operator.COMPNEQ;
		case "sle":
		case "ule":
			return Operator.COMPLEQ;
		case "slt":
		case "ult":
			return Operator.COMPLT;
		case "sge":
		case "uge":
			return Operator.COMPGEQ;
		case "sgt":
		case "ugt":
			return Operator.COMPGT;
		default:
			throw new AssertionError("Unsupported operator: " + operatorValue);
		}
	}

	/**
	 * Handles the visit event for a compilation unit in the LLVM IR parse tree.
	 *
	 * This method initializes the location and creates the initial declarations for the Boogie translation. It then
	 * visits all children of the compilation unit context to process function definitions and global variable
	 * definitions.
	 *
	 * @param ctx The parse tree context for the compilation unit.
	 * @return null, as this method does not return any value.
	 */
	@Override
	public FunctionBody visitCompilationUnit(final LLVMIRParser.CompilationUnitContext ctx) {
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
	public FunctionBody visitFuncDef(final LLVMIRParser.FuncDefContext ctx) throws AssertionError {
		final FunctionBody body = new FunctionBody();
		body.addFuncLocalVar(createVarDecWithPrimType("int", mLabelIdentifier, mLocation));

		body.addFuncLocalVar(createVarDecWithPrimType("int", mUndefIdentifier, mLocation));
		final VariableLHS undefVar = new VariableLHS(mLocation, mUndefIdentifier);
		final HavocStatement havocStmt = new HavocStatement(mLocation, new VariableLHS[] { undefVar });
		body.addFuncBlock(havocStmt);

		for (final ParseTree child : ctx.children) {
			final FunctionBody childBody = child.accept(this);
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
		final List<LLVMIRParser.BasicBlockContext> basicBlocks = ctx.basicBlock();
		for (final LLVMIRParser.BasicBlockContext childCtx : ctx.basicBlock()) {
			final FunctionBody childBody = visit(childCtx);
			if (childBody != null) {
				body.merge(childBody);
			}
		}
		return body;
	}

	@Override
	public FunctionBody visitBasicBlock(final LLVMIRParser.BasicBlockContext ctx) {
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());
		final FunctionBody body = new FunctionBody();

		final LLVMIRParser.FuncBodyContext funcBodyCtx = (LLVMIRParser.FuncBodyContext) ctx.getParent();
		final List<LLVMIRParser.BasicBlockContext> blocks = funcBodyCtx.basicBlock();
		final int index = blocks.indexOf(ctx);

		body.setCurrentLabelIndex(index);

		final String labelName = unifyIdentifier(ctx.LabelIdent().getText());
		final Label label = new Label(location, labelName, new NamedAttribute[] {});
		body.addLabel(labelName);
		body.addFuncBlock(label);

		for (final ParseTree child : ctx.children) {
			if (child.getChild(0) instanceof LLVMIRParser.CondBrTermContext
					|| child.getChild(0) instanceof LLVMIRParser.BrTermContext) {
				body.addFuncBlock(createLabelAssignment(location, body.getCurrentLabelIndex()));
			}
			final FunctionBody childBody = child.accept(this);
			if (childBody != null) {
				body.merge(childBody);
			}
		}

		if (!(index == blocks.size() - 1)) {
			body.addFuncBlock(createLabelAssignment(location, body.getCurrentLabelIndex()));
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
	public FunctionBody visitGlobalDef(final LLVMIRParser.GlobalDefContext ctx) {
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
	 * on the type of instruction.
	 *
	 * @param ctx The parse tree context for the local variable definition.
	 * @throws AssertionError if the instruction type is not supported.
	 */
	@Override
	public FunctionBody visitLocalDefInst(final LLVMIRParser.LocalDefInstContext ctx) {
		final FunctionBody body = new FunctionBody();
		final String identifier = unifyIdentifier(ctx.LocalIdent().getText());
		final LLVMIRParser.ValueInstructionContext instructionType = ctx.valueInstruction();
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		if (instructionType.loadInst() != null) {
			final LLVMIRParser.TypeContext variableType = instructionType.loadInst().type();
			if (variableType.intType() != null) {
				body.addFuncLocalVar(createVarDecWithPrimType("int", identifier, location));
				final VariableLHS varLhs = new VariableLHS(location, identifier);

				String loadVarIdentifier = null;
				if (instructionType.loadInst().typeValue().value().LocalIdent() != null) {
					loadVarIdentifier = unifyIdentifier(
							instructionType.loadInst().typeValue().value().LocalIdent().getText());
				} else if (instructionType.loadInst().typeValue().value().constant() != null) {
					loadVarIdentifier = instructionType.loadInst().typeValue().value().constant().GlobalIdent()
							.getText();
				} else {
					throw new AssertionError("Something went wrong while parsing the load instruction:");
				}

				final IdentifierExpression loadVarExpr = new IdentifierExpression(location,
						unifyIdentifier(loadVarIdentifier));
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { loadVarExpr });
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
			final Operator operator = getCompOperatorFromOperatorValue(instructionType.iCmpInst().iPred().getText());

			final LLVMIRParser.ValueContext leftOperandType = instructionType.iCmpInst().typeValue().value();
			leftExpr = getExpressionFromValue(leftOperandType, location);

			final LLVMIRParser.ValueContext rightOperandType = instructionType.iCmpInst().value();
			rightExpr = getExpressionFromValue(rightOperandType, location);

			final VariableLHS varLhs = new VariableLHS(null, identifier);
			final BinaryExpression binaryExpr = new BinaryExpression(location, operator, leftExpr, rightExpr);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { binaryExpr });
			body.addFuncBlock(assignment);
		} else if (instructionType.phiInst() != null) {
			body.addFuncLocalVar(createVarDecWithPrimType("bool", identifier, location));
			for (final LLVMIRParser.IncContext inc : instructionType.phiInst().inc()) {
				final String incIdentifier = unifyIdentifier(inc.LocalIdent().getText());
				final int labelIndex = getLabelIndexFromFuncBody(ctx, incIdentifier);
				final IdentifierExpression incExpr = new IdentifierExpression(location, mLabelIdentifier);
				final IntegerLiteral labelIndexLiteral = new IntegerLiteral(location, Integer.toString(labelIndex));
				final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.COMPEQ, incExpr,
						labelIndexLiteral);
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { getExpressionFromValue(inc.value(), location) });
				final IfStatement ifStmt = new IfStatement(location, binaryExpr, new Statement[] { assignment },
						new Statement[] {});
				body.addFuncBlock(ifStmt);
			}
		} else if (instructionType.zExtInst() != null) {
			body.addFuncLocalVar(createVarDecWithPrimType("int", identifier, location));
			final String type = instructionType.zExtInst().typeValue().firstClassType().concreteType().intType()
					.getText();
			if (type.equals("i1")) {
				final IntegerLiteral zeroLiteral = new IntegerLiteral(location, "0");
				final IntegerLiteral oneLiteral = new IntegerLiteral(location, "1");
				final VariableLHS zeroVarLhs = new VariableLHS(location, identifier);
				final VariableLHS oneVarLhs = new VariableLHS(location, identifier);
				final AssignmentStatement elseAssignment = new AssignmentStatement(location,
						new LeftHandSide[] { zeroVarLhs }, new Expression[] { zeroLiteral });
				final AssignmentStatement thenAssignment = new AssignmentStatement(location,
						new LeftHandSide[] { oneVarLhs }, new Expression[] { oneLiteral });
				final IfStatement ifStmt = new IfStatement(location,
						getExpressionFromValue(instructionType.zExtInst().typeValue().value(), location),
						new Statement[] { thenAssignment }, new Statement[] { elseAssignment });
				body.addFuncBlock(ifStmt);
			} else {
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] {
								getExpressionFromValue(instructionType.zExtInst().typeValue().value(), location) });
				body.addFuncBlock(assignment);
			}

		} else if (instructionType.addInst() != null) {
			body.addFuncLocalVar(createVarDecWithPrimType("int", identifier, location));
			body.addFuncBlock(
					createArithmeticAssignment(location, identifier, instructionType.addInst().typeValue().value(),
							instructionType.addInst().value(), Operator.ARITHPLUS));
		} else if (instructionType.sDivInst() != null) {
			body.addFuncLocalVar(createVarDecWithPrimType("int", identifier, location));
			body.addFuncBlock(
					createArithmeticAssignment(location, identifier, instructionType.sDivInst().typeValue().value(),
							instructionType.sDivInst().value(), Operator.ARITHDIV));
		} else if (instructionType.subInst() != null) {
			body.addFuncLocalVar(createVarDecWithPrimType("int", identifier, location));
			body.addFuncBlock(
					createArithmeticAssignment(location, identifier, instructionType.subInst().typeValue().value(),
							instructionType.subInst().value(), Operator.ARITHMINUS));
		} else if (instructionType.mulInst() != null) {
			body.addFuncLocalVar(createVarDecWithPrimType("int", identifier, location));
			body.addFuncBlock(
					createArithmeticAssignment(location, identifier, instructionType.mulInst().typeValue().value(),
							instructionType.mulInst().value(), Operator.ARITHMUL));
		} else if (instructionType.allocaInst() != null) {
			body.addFuncLocalVar(createVarDecWithPrimType("int", identifier, location));
		} else if (instructionType.callInst() != null) {
			final String callIdentifier = instructionType.callInst().value().constant().getText();
			if (callIdentifier.equals("@__VERIFIER_nondet_int") || callIdentifier.equals("@__VERIFIER_nondet_short")
					|| callIdentifier.equals("@__VERIFIER_nondet_ulong")
					|| callIdentifier.equals("@__VERIFIER_nondet_uint128")
					|| callIdentifier.equals("@__VERIFIER_nondet_char")
					|| callIdentifier.equals("@__VERIFIER_nondet_uchar")) {
				body.addFuncLocalVar(createVarDecWithPrimType("int", identifier, location));
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final HavocStatement havocStmt = new HavocStatement(location, new VariableLHS[] { varLhs });
				body.addFuncBlock(havocStmt);
			}
		} else if (instructionType.selectInst() != null) {
			final Expression ifExpr = getExpressionFromValue(instructionType.selectInst().typeValue(0).value(),
					location);
			final Expression thenExpr = getExpressionFromValue(instructionType.selectInst().typeValue(1).value(),
					location);
			final Expression elseExpr = getExpressionFromValue(instructionType.selectInst().typeValue(2).value(),
					location);
			final String type = instructionType.selectInst().typeValue(1).firstClassType().concreteType().intType()
					.getText();
			if (type.equals("i1")) {
				body.addFuncLocalVar(createVarDecWithPrimType("bool", identifier, location));
			} else {
				body.addFuncLocalVar(createVarDecWithPrimType("int", identifier, location));
			}
			final VariableLHS thenVarLhs = new VariableLHS(location, identifier);
			final VariableLHS elseVarLhs = new VariableLHS(location, identifier);
			final AssignmentStatement thenAssignment = new AssignmentStatement(location,
					new LeftHandSide[] { thenVarLhs }, new Expression[] { thenExpr });
			final AssignmentStatement elseAssignment = new AssignmentStatement(location,
					new LeftHandSide[] { elseVarLhs }, new Expression[] { elseExpr });
			final IfStatement ifStmt = new IfStatement(location, ifExpr, new Statement[] { thenAssignment },
					new Statement[] { elseAssignment });
			body.addFuncBlock(ifStmt);
		}

		else {
			// TODO: Support for other instructions
			throw new AssertionError("The support for the given instruction is not implemented yet.");
		}
		return body;
	}

	/**
	 * Handles the visit event for a branch terminator in the LLVM IR parse tree.
	 *
	 * This method processes the branch terminator and creates a GotoStatement to jump to the specified label.
	 *
	 * @param ctx The parse tree context for the branch terminator.
	 * @return A FunctionBody object containing the GotoStatement.
	 */
	@Override
	public FunctionBody visitBrTerm(final LLVMIRParser.BrTermContext ctx) {
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());
		final FunctionBody body = new FunctionBody();
		final String labelIdentifier = unifyIdentifier(ctx.label().LocalIdent().getText());
		final GotoStatement gotoStmt = new GotoStatement(location, new String[] { labelIdentifier });
		body.addFuncBlock(gotoStmt);

		return body;
	}

	/**
	 * Handles the visit event for a conditional branch terminator in the LLVM IR parse tree.
	 *
	 * This method processes the conditional branch terminator and creates an IfStatement to handle the condition, along
	 * with GotoStatements for the true and false branches.
	 *
	 * @param ctx The parse tree context for the conditional branch terminator.
	 * @return A FunctionBody object containing the IfStatement and GotoStatements.
	 */
	@Override
	public FunctionBody visitCondBrTerm(final LLVMIRParser.CondBrTermContext ctx) {
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());
		final FunctionBody body = new FunctionBody();

		final String variableIdentifier = unifyIdentifier(ctx.value().LocalIdent().getText());
		final String thenLabelIdentifier = unifyIdentifier(ctx.label(0).LocalIdent().getText());
		final String elseLabelIdentifier = unifyIdentifier(ctx.label(1).LocalIdent().getText());
		final GotoStatement thenGoto = new GotoStatement(location, new String[] { thenLabelIdentifier });
		final GotoStatement elseGoto = new GotoStatement(location, new String[] { elseLabelIdentifier });
		final IdentifierExpression variableExpr = new IdentifierExpression(location, variableIdentifier);
		final IfStatement ifStmt = new IfStatement(location, variableExpr, new Statement[] { thenGoto },
				new Statement[] { elseGoto });
		body.addFuncBlock(ifStmt);

		return body;
	}

	/**
	 * Handles the visit event for a store instruction in the LLVM IR parse tree.
	 *
	 * This method processes the store instruction and creates an AssignmentStatement to assign a value to a variable.
	 *
	 * @param ctx The parse tree context for the store instruction.
	 * @return A FunctionBody object containing the AssignmentStatement.
	 */
	@Override
	public FunctionBody visitStoreInst(final LLVMIRParser.StoreInstContext ctx) {
		final FunctionBody body = new FunctionBody();
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		final String identifier = unifyIdentifier(ctx.typeValue(1).value().LocalIdent().getText());
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
				new Expression[] { getExpressionFromValue(ctx.typeValue(0).value(), location) });
		body.addFuncBlock(assignment);

		return body;
	}

	@Override
	public FunctionBody visitCallInst(final LLVMIRParser.CallInstContext ctx) {
		final FunctionBody body = new FunctionBody();
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		final String callIdentifier = ctx.value().constant().getText();
		if (callIdentifier.equals("@__assert_fail")) {
			final BooleanLiteral boolLit = new BooleanLiteral(location, false);
			final AssertStatement assertStmt = new AssertStatement(location, new NamedAttribute[] {}, boolLit);
			final Check chk = new Check(Spec.ASSERT);
			chk.annotate(assertStmt);
			body.addFuncBlock(assertStmt);
		}

		return body;
	}
}
