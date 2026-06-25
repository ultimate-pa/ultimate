/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Lars Nitzke (lars.nitzke@outlook.com)
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.output;

import java.io.PrintWriter;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ParentEdge;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;

/**
 * Writes pretty-printed representations of Boogie AST nodes to an output stream.
 *
 * @author hoenicke
 * @author Dominik Klumpp (klumpp@lix.polytechnique.fr)
 */
public class BoogieOutput implements AutoCloseable {
	protected static final int PRECEDENCE_IFF = 0;
	protected static final int PRECEDENCE_IMPLIES = 1;
	protected static final int PRECEDENCE_LOGICAL_OR = 3;
	protected static final int PRECEDENCE_LOGICAL_AND = 4;
	protected static final int PRECEDENCE_COMPARISON = 5;
	protected static final int PRECEDENCE_BITVEC_CONCAT = 6;
	protected static final int PRECEDENCE_ADDITION = 7;
	protected static final int PRECEDENCE_MULTIPLICATION = 8;
	protected static final int PRECEDENCE_UNARY_MINUS_NEGATION = 9;
	protected static final int PRECEDENCE_ACCESS = 10;
	protected static final int PRECEDENCE_OLD = 11;

	protected static final int PRECEDENCE_TYPE_NAMED = 0;
	protected static final int PRECEDENCE_TYPE_STRUCT_ARRAY = 1;

	protected final PrintWriter mWriter;

	public BoogieOutput(final PrintWriter output) {
		mWriter = output;
	}

	public void printBoogieProgram(final Unit unit) {
		for (final Declaration d : unit.getDeclarations()) {
			switch (d) {
			case final Axiom a -> printAxiom(a);
			case final ConstDeclaration c -> printConstDeclaration(c);
			case final FunctionDeclaration f -> printFunctionDeclaration(f);
			case final Procedure p -> printProcedure(p);
			case final TypeDeclaration t -> printTypeDeclaration(t);
			case final VariableDeclaration v -> printVariableDeclaration(v);
			}
		}
	}

	public void printExpression(final Expression expr) {
		printExpression(expr, 0);
	}

	/**
	 * Print a given expression.
	 *
	 * @param expr
	 *            the expression to print.
	 * @param precedence
	 *            the precedence of the surrounding operator (see the {@code PRECEDENCE_*} constants defined above).
	 */
	protected void printExpression(final Expression expr, int precedence) {
		switch (expr) {
		case final BinaryExpression binexpr -> {
			final String op = getOperatorString(binexpr.getOperator());
			final int opPrec = getOperatorPrecedence(binexpr.getOperator());
			final int lPrec, rPrec;
			switch (binexpr.getOperator()) {
			case LOGICIFF, LOGICIMPLIES:
				lPrec = opPrec + 1;
				rPrec = opPrec;
				break;
			case BITVECCONCAT, ARITHPLUS, ARITHMINUS, ARITHMUL, ARITHDIV, ARITHMOD:
				lPrec = opPrec;
				rPrec = opPrec + 1;
				break;
			case COMPEQ, COMPNEQ, COMPLT, COMPLEQ, COMPGT, COMPGEQ, COMPPO:
				lPrec = opPrec + 1;
				rPrec = opPrec + 1;
				break;

			case LOGICOR:
				lPrec = PRECEDENCE_LOGICAL_AND + 1;
				rPrec = opPrec;
				break;
			case LOGICAND:
				if (precedence == PRECEDENCE_LOGICAL_OR) {
					precedence = opPrec + 1;
				}
				lPrec = opPrec + 1;
				rPrec = opPrec;
				break;
			default:
				throw new IllegalArgumentException(expr.toString());
			}
			if (precedence > opPrec) {
				mWriter.print("(");
			}
			printExpression(binexpr.getLeft(), lPrec);
			mWriter.print(op);
			printExpression(binexpr.getRight(), rPrec);
			if (precedence > opPrec) {
				mWriter.print(")");
			}
		}
		case final UnaryExpression unexpr -> {
			final String op = getOperatorString(unexpr.getOperator());
			final int opPrec = getOperatorPrecedence(unexpr.getOperator());
			if (precedence > opPrec) {
				mWriter.print("(");
			}
			mWriter.print(op);
			if (unexpr.getOperator() == UnaryExpression.Operator.OLD) {
				mWriter.print("(");
				printExpression(unexpr.getExpr());
				mWriter.print(")");
			} else {
				printExpression(unexpr.getExpr(), opPrec);
			}
			if (precedence > opPrec) {
				mWriter.print(")");
			}
		}
		case final BitVectorAccessExpression bvexpr -> {
			if (precedence > PRECEDENCE_ACCESS) {
				mWriter.print("(");
			}
			printExpression(bvexpr.getBitvec(), PRECEDENCE_ACCESS);
			mWriter.print("[");
			mWriter.print(bvexpr.getEnd());
			mWriter.print(":");
			mWriter.print(bvexpr.getStart());
			mWriter.print("]");
			if (precedence > PRECEDENCE_ACCESS) {
				mWriter.print(")");
			}
		}
		case final StructAccessExpression strexpr -> {
			if (precedence > PRECEDENCE_ACCESS) {
				mWriter.print("(");
			}
			printExpression(strexpr.getStruct(), PRECEDENCE_ACCESS);
			mWriter.print("!");
			mWriter.print(strexpr.getField());
			if (precedence > PRECEDENCE_ACCESS) {
				mWriter.print(")");
			}
		}
		case final ArrayAccessExpression arrexpr -> {
			if (precedence > PRECEDENCE_ACCESS) {
				mWriter.print("(");
			}
			printExpression(arrexpr.getArray(), PRECEDENCE_ACCESS);
			mWriter.print("[");
			printExpressionList(arrexpr.getIndices());
			mWriter.print("]");
			if (precedence > PRECEDENCE_ACCESS) {
				mWriter.print(")");
			}
		}
		case final ArrayStoreExpression arrexpr -> {
			if (precedence > PRECEDENCE_ACCESS) {
				mWriter.print("(");
			}
			printExpression(arrexpr.getArray(), PRECEDENCE_ACCESS);
			mWriter.print("[");
			printExpressionList(arrexpr.getIndices());
			mWriter.print(" := ");
			printExpression(arrexpr.getValue());
			mWriter.print("]");
			if (precedence > PRECEDENCE_ACCESS) {
				mWriter.print(")");
			}
		}
		case final BitvecLiteral bvlit -> {
			mWriter.print(bvlit.getValue());
			mWriter.print("bv");
			mWriter.print(bvlit.getLength());
		}
		case final IntegerLiteral intlit -> mWriter.print(intlit.getValue());
		case final RealLiteral reallit -> {
			final String value = reallit.getValue();
			String realValue;
			try {
				// produce decimal literal for integer values, e.g., write 1.0 if RealLiteral is 1
				realValue = String.valueOf(Double.parseDouble(value));
			} catch (final NumberFormatException ex) {
				realValue = value;
			}
			mWriter.print(realValue);
		}
		case final BooleanLiteral boollit -> mWriter.print(boollit.getValue());
		case final StringLiteral strlit -> {
			mWriter.print('"');
			mWriter.print(strlit.getValue());
			mWriter.print('"');
		}
		case final StructConstructor struct -> {
			String comma = "";
			mWriter.print("{ ");
			final String[] fieldNames = struct.getFieldIdentifiers();
			final Expression[] fieldExprs = struct.getFieldValues();
			for (int i = 0; i < fieldNames.length; i++) {
				mWriter.print(comma);
				mWriter.print(fieldNames[i]);
				mWriter.print(": ");
				printExpression(fieldExprs[i]);
				comma = ", ";
			}
			mWriter.print(" }");
		}
		case final WildcardExpression wildExpr -> mWriter.print("*");
		case final IdentifierExpression id -> mWriter.print(id.getIdentifier());
		case final FunctionApplication app -> {
			mWriter.print(app.getIdentifier());
			mWriter.print("(");
			printExpressionList(app.getArguments());
			mWriter.print(")");
		}
		case final IfThenElseExpression ite -> {
			/* we always append parentheses, just to be sure. */
			mWriter.print("(if ");
			printExpression(ite.getCondition());
			mWriter.print(" then ");
			printExpression(ite.getThenPart());
			mWriter.print(" else ");
			printExpression(ite.getElsePart());
			mWriter.print(")");
		}
		case final QuantifierExpression quant -> {
			mWriter.print("(");
			mWriter.print(quant.isUniversal() ? "forall" : "exists");
			final String[] typeParams = quant.getTypeParams();
			if (typeParams.length > 0) {
				mWriter.print(" <");
				printStringList(typeParams);
				mWriter.print(">");
			}
			if (quant.getParameters().length > 0) {
				mWriter.print(" ");
				printVarList(quant.getParameters());
			}
			mWriter.print(" :: ");
			printAttributesWithTrailingSpace(quant.getAttributes());
			printExpression(quant.getSubformula());
			mWriter.print(")");
		}
		}
	}

	protected static String getOperatorString(final UnaryExpression.Operator operator) {
		return switch (operator) {
		case ARITHNEGATIVE -> "-";
		case LOGICNEG -> "!";
		case OLD -> "old";
		};
	}

	protected static String getOperatorString(final BinaryExpression.Operator operator) {
		return switch (operator) {
		case ARITHDIV -> " / ";
		case ARITHMINUS -> " - ";
		case ARITHMOD -> " % ";
		case ARITHMUL -> " * ";
		case ARITHPLUS -> " + ";
		case BITVECCONCAT -> " ++ ";
		case COMPEQ -> " == ";
		case COMPGEQ -> " >= ";
		case COMPGT -> " > ";
		case COMPLEQ -> " <= ";
		case COMPLT -> " < ";
		case COMPNEQ -> " != ";
		case COMPPO -> " <: ";
		case LOGICAND -> " && ";
		case LOGICIFF -> " <==> ";
		case LOGICIMPLIES -> " ==> ";
		case LOGICOR -> " || ";
		};
	}

	protected static int getOperatorPrecedence(final UnaryExpression.Operator operator) {
		return switch (operator) {
		case ARITHNEGATIVE -> PRECEDENCE_UNARY_MINUS_NEGATION;
		case LOGICNEG -> PRECEDENCE_UNARY_MINUS_NEGATION;
		case OLD -> PRECEDENCE_OLD;
		};
	}

	protected static int getOperatorPrecedence(final BinaryExpression.Operator operator) {
		return switch (operator) {
		case LOGICIFF -> PRECEDENCE_IFF;
		case LOGICIMPLIES -> PRECEDENCE_IMPLIES;
		case LOGICOR -> PRECEDENCE_LOGICAL_OR;
		case LOGICAND -> PRECEDENCE_LOGICAL_AND;
		case COMPEQ, COMPNEQ, COMPLT, COMPLEQ, COMPGT, COMPGEQ, COMPPO -> PRECEDENCE_COMPARISON;
		case BITVECCONCAT -> PRECEDENCE_BITVEC_CONCAT;
		case ARITHPLUS, ARITHMINUS -> PRECEDENCE_ADDITION;
		case ARITHMUL, ARITHDIV, ARITHMOD -> PRECEDENCE_MULTIPLICATION;
		};
	}

	public void printType(final ASTType type) {
		printType(type, 0);
	}

	protected void printType(final ASTType type, final int precedence) {
		switch (type) {
		case final NamedType nt -> {
			final ASTType[] args = nt.getTypeArgs();

			if (precedence > PRECEDENCE_TYPE_NAMED && args.length > 0) {
				mWriter.print("(");
			}
			mWriter.print(nt.getName());
			for (int i = 0; i < args.length; i++) {
				mWriter.print(" ");
				printType(args[i], i < args.length - 1 ? 2 : 1);
			}
			if (precedence > PRECEDENCE_TYPE_NAMED && args.length > 0) {
				mWriter.print(")");
			}
		}
		case final ArrayType at -> {
			if (precedence > PRECEDENCE_TYPE_STRUCT_ARRAY) {
				mWriter.print("(");
			}
			if (at.getTypeParams().length > 0) {
				mWriter.print("<");
				printStringList(at.getTypeParams());
				mWriter.print(">");
			}
			mWriter.print("[");
			printList(at.getIndexTypes(), this::printType);
			mWriter.print("]");
			printType(at.getValueType(), 0);
			if (precedence > PRECEDENCE_TYPE_STRUCT_ARRAY) {
				mWriter.print(")");
			}
		}
		case final StructType st -> {
			if (precedence > PRECEDENCE_TYPE_STRUCT_ARRAY) {
				mWriter.print("(");
			}
			mWriter.print("{ ");
			printVarList(st.getFields());
			mWriter.print(" }");
			if (precedence > PRECEDENCE_TYPE_STRUCT_ARRAY) {
				mWriter.print(")");
			}
		}
		case final PrimitiveType primitive -> mWriter.print(primitive.getName());
		}
	}

	private void printAttributesWithTrailingSpace(final Attribute... attributes) {
		if (attributes == null || attributes.length == 0) {
			return;
		}
		printAttributes(attributes);
		mWriter.print(" ");
	}

	public void printAttributes(final Attribute... attributes) {
		if (attributes == null) {
			return;
		}
		String space = "";
		for (final Attribute a : attributes) {
			mWriter.print(space);
			switch (a) {
			case final NamedAttribute attr -> {
				mWriter.print("{ :");
				mWriter.print(attr.getName());
				if (attr.getValues().length > 0) {
					mWriter.print(" ");
					printExpressionList(attr.getValues());
				}
				mWriter.print(" }");
			}
			case final Trigger trig -> {
				mWriter.print("{ ");
				printExpressionList(trig.getTriggers());
				mWriter.print(" }");
			}
			}
			space = " ";
		}
	}

	/**
	 * Print the string representation of vls (comma separated list of declarations).
	 *
	 * @param vls
	 *            the variable declaration that are printed.
	 */
	public void printVarList(final VarList... vls) {
		String comma = "";
		for (final VarList vl : vls) {
			mWriter.print(comma);
			if (vl.getIdentifiers().length > 0) {
				/*
				 * identifiers array can only be empty for function parameters (unnamed parameter).
				 */
				printStringList(vl.getIdentifiers());
				mWriter.print(" : ");
			}
			printType(vl.getType());
			if (vl.getWhereClause() != null) {
				mWriter.print(" where ");
				printExpression(vl.getWhereClause());
			}
			comma = ", ";
		}
	}

	public void printTypeDeclaration(final TypeDeclaration decl) {
		mWriter.print("type ");
		printAttributesWithTrailingSpace(decl.getAttributes());
		final ASTType synonym = decl.getSynonym();
		if (synonym == null && decl.isFinite()) {
			mWriter.print("finite ");
		}
		mWriter.print(decl.getIdentifier());
		for (final String args : decl.getTypeParams()) {
			mWriter.print(" ");
			mWriter.print(args);
		}
		if (synonym != null) {
			mWriter.print(" = ");
			printType(synonym);
		}
		mWriter.print(";");
	}

	public void printFunctionDeclaration(final FunctionDeclaration decl) {
		mWriter.print("function ");
		printAttributesWithTrailingSpace(decl.getAttributes());
		mWriter.print(decl.getIdentifier());
		if (decl.getTypeParams().length > 0) {
			mWriter.print("<");
			printStringList(decl.getTypeParams());
			mWriter.print(">");
		}
		mWriter.print("(");
		printVarList(decl.getInParams());
		mWriter.print(") returns (");
		printVarList(decl.getOutParam());
		mWriter.print(")");
		if (decl.getBody() != null) {
			mWriter.print(" { ");
			printExpression(decl.getBody());
			mWriter.print(" }");
		} else {
			mWriter.print(";");
		}
	}

	public void printProcedure(final Procedure decl) {
		if (decl.getSpecification() != null) {
			mWriter.print("procedure ");
		} else {
			mWriter.print("implementation ");
		}
		printAttributesWithTrailingSpace(decl.getAttributes());
		mWriter.print(decl.getIdentifier());
		if (decl.getTypeParams().length > 0) {
			mWriter.print("<");
			printStringList(decl.getTypeParams());
			mWriter.print(">");
		}
		mWriter.print("(");
		printVarList(decl.getInParams());
		mWriter.print(") returns (");
		printVarList(decl.getOutParams());
		mWriter.print(")");
		if (decl.getBody() == null) {
			mWriter.print(";");
		}
		if (decl.getSpecification() != null) {
			mWriter.println();
			for (final Specification spec : decl.getSpecification()) {
				printSpecification(spec);
			}
		}
		if (decl.getBody() != null) {
			mWriter.println("{");
			printBody(decl.getBody());
			mWriter.println("}");
		}
		mWriter.println();
	}

	public void printSpecification(final Specification spec) {
		if (spec.isFree()) {
			mWriter.print("free ");
		}
		switch (spec) {
		case final RequiresSpecification requires:
			mWriter.print("requires ");
			printExpression(requires.getFormula());
			break;
		case final EnsuresSpecification ensures:
			mWriter.print("ensures ");
			printExpression(ensures.getFormula());
			break;
		case final ModifiesSpecification modifies:
			mWriter.print("modifies ");
			printLHSList(modifies.getIdentifiers());
			break;
		case final LoopInvariantSpecification invariant:
			mWriter.print("invariant ");
			printExpression(invariant.getFormula());
			break;
		}
		mWriter.println(";");
	}

	public void printBody(final Body body) {
		for (final VariableDeclaration decl : body.getLocalVars()) {
			printVariableDeclaration(decl, "    ");
		}
		if (body.getLocalVars().length > 0) {
			mWriter.println();
		}
		printBlock(body.getBlock(), "");
	}

	public void printBlock(final Statement[] block) {
		printBlock(block, "");
	}

	/**
	 * Print block.
	 *
	 * @param block
	 *            the block to print.
	 * @param indent
	 *            the current indent level.
	 */
	public void printBlock(final Statement[] block, final String indent) {
		final String nextIndent = indent + "    ";
		for (final Statement s : block) {
			if (s instanceof final Label l) {
				// SF: Labels aren't on the first column anymore, they are
				// treated as pragmas if they are. Added " "
				mWriter.print(indent + "  " + l.getName());
				if (l.getAttributes() != null && l.getAttributes().length > 0) {
					mWriter.print(" ");
					printAttributes(l.getAttributes());
					mWriter.print(" ");
				}
				mWriter.println(":");
			} else {
				printStatement(s, nextIndent);
			}
		}

	}

	public void printStatement(final Statement s) {
		printStatement(s, "");
	}

	/**
	 * Print the statement.
	 *
	 * @param s
	 *            the statement to print.
	 * @param indent
	 *            The current identation
	 */
	public void printStatement(final Statement s, final String indent) {
		mWriter.print(indent);
		switch (s) {
		case final AssertStatement assertstmt -> {
			mWriter.print("assert ");
			printAttributesWithTrailingSpace(assertstmt.getAttributes());
			printExpression(assertstmt.getFormula());
			mWriter.print(";");
		}
		case final AssumeStatement assumestmt -> {
			mWriter.print("assume ");
			printAttributesWithTrailingSpace(assumestmt.getAttributes());
			printExpression(assumestmt.getFormula());
			mWriter.print(";");
		}
		case final HavocStatement havoc -> {
			mWriter.print("havoc ");
			printLHSList(havoc.getIdentifiers());
			mWriter.print(";");
		}
		case final AssignmentStatement stmt -> {
			printLHSList(stmt.getLhs());
			mWriter.print(" := ");
			printExpressionList(stmt.getRhs());
			mWriter.print(";");
		}
		case final CallStatement call -> {
			mWriter.print("call ");
			printAttributesWithTrailingSpace(call.getAttributes());
			if (call.isForall()) {
				mWriter.print("forall ");
			}
			if (call.getLhs().length > 0) {
				printLHSList(call.getLhs());
				mWriter.print(" := ");
			}
			mWriter.print(call.getMethodName());
			mWriter.print("(");
			printExpressionList(call.getArguments());
			mWriter.print(");");
		}
		case final ForkStatement fork -> {
			mWriter.print("fork ");
			printExpressionList(fork.getThreadID());
			mWriter.print(" ");
			mWriter.print(fork.getProcedureName());
			mWriter.print("(");
			printExpressionList(fork.getArguments());
			mWriter.print(");");
		}
		case final JoinStatement join -> {
			mWriter.print("join ");
			printExpressionList(join.getThreadID());
			if (join.getLhs().length > 0) {
				mWriter.print(" assign ");
				printLHSList(join.getLhs());
			}
			mWriter.print(";");
		}
		case final BreakStatement breakStmt -> {
			final String label = breakStmt.getLabel();
			mWriter.print("break");
			if (label != null) {
				mWriter.print(" ");
				mWriter.print(label);
			}
			mWriter.print(";");
		}
		case final ReturnStatement retStmt -> mWriter.print("return;");
		case final GotoStatement gotoStmt -> {
			mWriter.print("goto ");
			printStringList(gotoStmt.getLabels());
			mWriter.print(";");
		}
		case IfStatement stmt -> {
			Statement[] elsePart;
			while (true) {
				mWriter.print("if (");
				printExpression(stmt.getCondition());
				mWriter.println(") {");
				printBlock(stmt.getThenPart(), indent);
				mWriter.print(indent);
				mWriter.print("}");
				elsePart = stmt.getElsePart();
				if (elsePart.length != 1 || !(elsePart[0] instanceof final IfStatement elseIf)) {
					break;
				}
				stmt = elseIf;
				mWriter.print(" else ");
			}
			if (elsePart.length > 0) {
				mWriter.println(" else {");
				printBlock(stmt.getElsePart(), indent);
				mWriter.print(indent);
				mWriter.print("}");
			}
		}
		case final WhileStatement stmt -> {
			mWriter.print("while (");
			printExpression(stmt.getCondition());
			mWriter.println(")");
			for (final LoopInvariantSpecification spec : stmt.getInvariants()) {
				mWriter.print(indent);
				mWriter.print("    ");
				printSpecification(spec);
			}
			mWriter.print(indent);
			mWriter.println("{");
			printBlock(stmt.getBody(), indent);
			mWriter.print(indent);
			mWriter.print("}");
		}
		case final Label label -> {
			mWriter.print(label.getName());
			mWriter.print(":");
		}
		case final AtomicStatement stmt -> {
			mWriter.println("atomic {");
			printBlock(stmt.getBody(), indent);
			mWriter.print(indent);
			mWriter.print("}");
		}
		}
		mWriter.println();
	}

	protected void printLHS(final LeftHandSide lhs) {
		switch (lhs) {
		case final VariableLHS varLHS -> mWriter.print(varLHS.getIdentifier());
		case final ArrayLHS arrlhs -> {
			printLHS(arrlhs.getArray());
			mWriter.print("[");
			printExpressionList(arrlhs.getIndices());
			mWriter.print("]");
		}
		case final StructLHS strlhs -> {
			printLHS(strlhs.getStruct());
			mWriter.print("!");
			mWriter.print(strlhs.getField());
		}
		}
	}

	public void printAxiom(final Axiom decl) {
		mWriter.print("axiom ");
		printAttributesWithTrailingSpace(decl.getAttributes());
		printExpression(decl.getFormula());
		mWriter.print(";");
	}

	/**
	 * Print variable declaration.
	 *
	 * @param decl
	 *            the variable declaration to print.
	 * @param indent
	 *            the current indent level.
	 */
	public void printVariableDeclaration(final VariableDeclaration decl, final String indent) {
		mWriter.print(indent);
		mWriter.print("var ");
		printAttributesWithTrailingSpace(decl.getAttributes());
		printVarList(decl.getVariables());
		mWriter.println(";");
	}

	public void printVariableDeclaration(final VariableDeclaration decl) {
		printVariableDeclaration(decl, "");
	}

	public void printConstDeclaration(final ConstDeclaration decl) {
		mWriter.print("const ");
		printAttributesWithTrailingSpace(decl.getAttributes());
		if (decl.isUnique()) {
			mWriter.print("unique ");
		}
		printVarList(decl.getVarList());
		if (decl.getParentInfo() != null) {
			mWriter.print(" <:");
			String comma = " ";
			for (final ParentEdge edge : decl.getParentInfo()) {
				mWriter.print(comma);
				if (edge.isUnique()) {
					mWriter.print("unique ");
				}
				mWriter.print(edge.getIdentifier());
				comma = ", ";
			}
		}
		if (decl.isComplete()) {
			mWriter.print(" complete");
		}
		mWriter.print(";");
	}

	protected void printStringList(final String[] list) {
		printList(list, mWriter::print);
	}

	protected void printExpressionList(final Expression[] expressions) {
		printList(expressions, this::printExpression);
	}

	protected void printLHSList(final LeftHandSide[] leftHandSides) {
		printList(leftHandSides, this::printLHS);
	}

	protected <T> void printList(final T[] list, final Consumer<T> printer) {
		String comma = "";
		for (final T item : list) {
			mWriter.print(comma);
			printer.accept(item);
			comma = ", ";
		}
	}

	@Override
	public void close() {
		mWriter.close();
	}
}
