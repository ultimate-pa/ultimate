package local.stalin.boogie.printer;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

import org.apache.log4j.Logger;

import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.core.api.StalinServices;
import local.stalin.model.IElement;
import local.stalin.model.boogie.ast.*;
import local.stalin.model.boogie.ast.wrapper.WrapperNode;

public class BoogiePrinterObserver implements IUnmanagedObserver {
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);

	PrintWriter writer;

	// @Override
	public boolean process(IElement root) {
		if (root instanceof WrapperNode) {
			try {
				writer = new PrintWriter(new FileWriter("foo.bpl"));
			} catch (IOException e) {
				s_Logger.error("Cannot open temporary file foo.bpl", e);
			}
			Unit unit = (Unit) ((WrapperNode) root).getBacking();
			for (Declaration d : unit.getDeclarations()) {
				if (d instanceof TypeDeclaration)
					printTypeDeclaration((TypeDeclaration) d);
				else if (d instanceof ConstDeclaration)
					printConstDeclaration((ConstDeclaration) d);
				else if (d instanceof VariableDeclaration)
					printVarDeclaration((VariableDeclaration) d, "");
				else if (d instanceof FunctionDeclaration)
					printFunctionDeclaration((FunctionDeclaration) d);
				else if (d instanceof Axiom)
					printAxiom((Axiom) d);
				else if (d instanceof Procedure)
					printProcedure((Procedure) d);
			}
			writer.flush();
			writer.close();
			return false;
		}
		return true;
	}

	private void appendExpression(StringBuilder sb, Expression expr,
			int precedence) {
		if (expr instanceof BinaryExpression) {
			BinaryExpression binexpr = (BinaryExpression) expr;
			int opPrec, lPrec, rPrec;
			String op;
			switch (binexpr.getOperator()) {
			case LOGICIFF:
				op = " <==> ";
				opPrec = 0;
				lPrec = 1;
				rPrec = 0;
				break;
			case LOGICIMPLIES:
				op = " ==> ";
				opPrec = 1;
				lPrec = 2;
				rPrec = 1;
				break;
			case LOGICOR:
				op = " || ";
				opPrec = 3;
				lPrec = 5;
				rPrec = 3;
				break;
			case LOGICAND:
				if (precedence == 3)
					precedence = 5;
				op = " && ";
				opPrec = 4;
				lPrec = 5;
				rPrec = 4;
				break;
			case COMPEQ:
				op = " == ";
				opPrec = 5;
				lPrec = 6;
				rPrec = 6;
				break;
			case COMPNEQ:
				op = " != ";
				opPrec = 5;
				lPrec = 6;
				rPrec = 6;
				break;
			case COMPLT:
				op = " < ";
				opPrec = 5;
				lPrec = 6;
				rPrec = 6;
				break;
			case COMPLEQ:
				op = " <= ";
				opPrec = 5;
				lPrec = 6;
				rPrec = 6;
				break;
			case COMPGT:
				op = " > ";
				opPrec = 5;
				lPrec = 6;
				rPrec = 6;
				break;
			case COMPGEQ:
				op = " >= ";
				opPrec = 5;
				lPrec = 6;
				rPrec = 6;
				break;
			case COMPPO:
				op = " <: ";
				opPrec = 5;
				lPrec = 6;
				rPrec = 6;
				break;
			case BITVECCONCAT:
				op = " ++ ";
				opPrec = 6;
				lPrec = 6;
				rPrec = 7;
				break;
			case ARITHPLUS:
				op = " + ";
				opPrec = 7;
				lPrec = 7;
				rPrec = 8;
				break;
			case ARITHMINUS:
				op = " - ";
				opPrec = 7;
				lPrec = 7;
				rPrec = 8;
				break;
			case ARITHMUL:
				op = " * ";
				opPrec = 8;
				lPrec = 8;
				rPrec = 9;
				break;
			case ARITHDIV:
				op = " / ";
				opPrec = 8;
				lPrec = 8;
				rPrec = 9;
				break;
			case ARITHMOD:
				op = " % ";
				opPrec = 8;
				lPrec = 8;
				rPrec = 9;
				break;
			default:
				throw new IllegalArgumentException(expr.toString());
			}
			if (precedence > opPrec)
				sb.append("(");
			appendExpression(sb, binexpr.getLeft(), lPrec);
			sb.append(op);
			appendExpression(sb, binexpr.getRight(), rPrec);
			if (precedence > opPrec)
				sb.append(")");
		} else if (expr instanceof UnaryExpression) {
			UnaryExpression unexpr = (UnaryExpression) expr;
			String op;
			int opPrec;
			switch (unexpr.getOperator()) {
			case ARITHNEGATIVE:
				op = "-";
				opPrec = 9;
				break;
			case LOGICNEG:
				op = "!";
				opPrec = 9;
				break;
			case OLD:
				op = "old";
				opPrec = 11;
				break;
			default:
				throw new IllegalArgumentException(expr.toString());
			}
			if (precedence > opPrec)
				sb.append("(");
			sb.append(op);
			if (op == "old") {
				sb.append("(");
				appendExpression(sb, unexpr.getExpr(), 0);
				sb.append(")");
			} else
				appendExpression(sb, unexpr.getExpr(), opPrec);
			if (precedence > opPrec)
				sb.append(")");
		} else if (expr instanceof BitVectorAccessExpression) {
			BitVectorAccessExpression bvexpr = (BitVectorAccessExpression) expr;
			if (precedence > 10)
				sb.append("(");
			appendExpression(sb, bvexpr.getBitvec(), 10);
			sb.append("[").append(bvexpr.getEnd()).append(":");
			sb.append(bvexpr.getStart()).append("]");
			if (precedence > 10)
				sb.append(")");
		} else if (expr instanceof ArrayAccessExpression) {
			ArrayAccessExpression arrexpr = (ArrayAccessExpression) expr;
			if (precedence > 10)
				sb.append("(");
			appendExpression(sb, arrexpr.getArray(), 10);
			sb.append("[");
			String comma = "";
			for (Expression indExpr : arrexpr.getIndices()) {
				sb.append(comma);
				appendExpression(sb, indExpr, 0);
				comma = ",";
			}
			sb.append("]");
			if (precedence > 10)
				sb.append(")");
		} else if (expr instanceof ArrayStoreExpression) {
			ArrayStoreExpression arrexpr = (ArrayStoreExpression) expr;
			if (precedence > 10)
				sb.append("(");
			appendExpression(sb, arrexpr.getArray(), 10);
			sb.append("[");
			String comma = "";
			for (Expression indExpr : arrexpr.getIndices()) {
				sb.append(comma);
				appendExpression(sb, indExpr, 0);
				comma = ",";
			}
			sb.append(" := ");
			appendExpression(sb, arrexpr.getValue(), 0);
			sb.append("]");
			if (precedence > 10)
				sb.append(")");
		} else if (expr instanceof BitvecLiteral) {
			BitvecLiteral bvlit = (BitvecLiteral) expr;
			sb.append(bvlit.getValue()).append("bv").append(bvlit.getLength());
		} else if (expr instanceof IntegerLiteral) {
			sb.append(((IntegerLiteral) expr).getValue());
		} else if (expr instanceof RealLiteral) {
			sb.append(((RealLiteral) expr).getValue());
		} else if (expr instanceof BooleanLiteral) {
			sb.append(((BooleanLiteral) expr).getValue());
		} else if (expr instanceof StringLiteral) {
			sb.append('"').append(((StringLiteral) expr).getValue())
					.append('"');
		} else if (expr instanceof WildcardExpression) {
			sb.append("*");
		} else if (expr instanceof IdentifierExpression) {
			sb.append(((IdentifierExpression) expr).getIdentifier());
		} else if (expr instanceof FunctionApplication) {
			FunctionApplication app = (FunctionApplication) expr;
			sb.append(app.getIdentifier()).append("(");
			String comma = "";
			for (Expression arg : app.getArguments()) {
				sb.append(comma);
				appendExpression(sb, arg, 0);
				comma = ", ";
			}
			sb.append(")");
		} else if (expr instanceof IfThenElseExpression) {
			IfThenElseExpression ite = (IfThenElseExpression) expr;
			/* we always append parentheses, just to be sure. */
			sb.append("(if ");
			appendExpression(sb, ite.getCondition(), 0);
			sb.append(" then ");
			appendExpression(sb, ite.getThenPart(), 0);
			sb.append(" else ");
			appendExpression(sb, ite.getElsePart(), 0);
			sb.append(")");
		} else if (expr instanceof QuantifierExpression) {
			QuantifierExpression quant = (QuantifierExpression) expr;
			sb.append("(");
			sb.append(quant.isUniversal() ? "forall" : "exists");
			String[] typeParams = quant.getTypeParams();
			if (typeParams.length > 0) {
				sb.append(" <");
				String comma = "";
				for (String t : typeParams) {
					sb.append(comma).append(t);
					comma = ",";
				}
				sb.append(">");
			}
			String comma = " ";
			for (VarList vl : quant.getParameters()) {
				sb.append(comma);
				comma = "";
				for (String id : vl.getIdentifiers()) {
					sb.append(comma).append(id);
					comma = ",";
				}
				sb.append(" : ");
				appendType(sb, vl.getType(), 0);
				comma = ", ";
			}
			sb.append(" :: ");
			appendAttributes(sb, quant.getAttributes());
			appendExpression(sb, quant.getSubformula(), 0);
			sb.append(")");
		} else {
			throw new IllegalArgumentException(expr.toString());
		}

	}

	private void appendType(StringBuilder sb, ASTType type, int precedence) {
		if (type instanceof NamedType) {
			NamedType nt = (NamedType) type;
			ASTType[] args = nt.getTypeArgs();

			if (precedence > 0 && args.length > 0)
				sb.append("(");
			sb.append(nt.getName());
			for (int i = 0; i < args.length; i++) {
				sb.append(" ");
				appendType(sb, args[i], i < args.length - 1 ? 2 : 1);
			}
			if (precedence > 0 && args.length > 0)
				sb.append(")");
		} else if (type instanceof ArrayType) {
			ArrayType at = (ArrayType) type;
			if (precedence > 1)
				sb.append("(");
			if (at.getTypeParams().length > 0) {
				String comma = "<";
				for (String id : at.getTypeParams()) {
					sb.append(comma).append(id);
					comma = ",";
				}
				sb.append(">");
			}
			String comma = "[";
			for (ASTType indexType : at.getIndexTypes()) {
				sb.append(comma);
				appendType(sb, indexType, 0);
				comma = ",";
			}
			sb.append("]");
			appendType(sb, at.getValueType(), 0);
			if (precedence > 1)
				sb.append(")");
		} else if (type instanceof PrimitiveType) {
			sb.append(((PrimitiveType) type).getName());
		}
	}

	private void appendAttributes(StringBuilder sb, Attribute[] attributes) {
		for (Attribute a : attributes) {
			if (a instanceof NamedAttribute) {
				NamedAttribute attr = (NamedAttribute) a;
				sb.append("{ :").append(attr.getName());
				String comma = " ";
				for (Expression value : attr.getValues()) {
					sb.append(comma);
					appendExpression(sb, value, 0);
					comma = ",";
				}
				sb.append(" } ");
			} else if (a instanceof Trigger) {
				sb.append("{ ");
				String comma = "";
				for (Expression value : ((Trigger) a).getTriggers()) {
					sb.append(comma);
					appendExpression(sb, value, 0);
					comma = ",";
				}
				sb.append(" } ");
			}
		}
	}

	private void printTypeDeclaration(TypeDeclaration decl) {
		StringBuilder sb = new StringBuilder();
		sb.append("type ");
		appendAttributes(sb, decl.getAttributes());
		if (decl.isFinite())
			sb.append("finite ");
		sb.append(decl.getIdentifier());
		for (String args : decl.getTypeParams())
			sb.append(" ").append(args);
		ASTType synonym = decl.getSynonym();
		if (synonym != null) {
			sb.append(" = ");
			appendType(sb, synonym, 0);
		}
		sb.append(";");
		writer.println(sb.toString());
	}

	private void printFunctionDeclaration(FunctionDeclaration decl) {
		StringBuilder sb = new StringBuilder();
		sb.append("function ");
		appendAttributes(sb, decl.getAttributes());
		sb.append(decl.getIdentifier());
		if (decl.getTypeParams().length > 0) {
			String comma = "<";
			for (String id : decl.getTypeParams()) {
				sb.append(comma).append(id);
				comma = ",";
			}
			sb.append(">");
		}
		sb.append("(");
		String comma = "";
		for (VarList vl : decl.getInParams()) {
			sb.append(comma);
			if (vl.getIdentifiers().length > 0)
				sb.append(vl.getIdentifiers()[0]).append(":");
			appendType(sb, vl.getType(), 0);
			comma = ", ";
		}
		sb.append(") returns (");
		VarList vl = decl.getOutParam();
		if (vl.getIdentifiers().length > 0)
			sb.append(vl.getIdentifiers()[0]).append(":");
		appendType(sb, vl.getType(), 0);
		sb.append(")");
		if (decl.getBody() != null) {
			sb.append(" { ");
			appendExpression(sb, decl.getBody(), 0);
			sb.append(" }");
		} else
			sb.append(";");
		writer.println(sb.toString());
	}

	private void printProcedure(Procedure decl) {
		StringBuilder sb = new StringBuilder();
		if (decl.getSpecification() != null) {
			sb.append("procedure ");
		} else {
			sb.append("implementation ");
		}
		appendAttributes(sb, decl.getAttributes());
		sb.append(decl.getIdentifier());
		if (decl.getTypeParams().length > 0) {
			String comma = "<";
			for (String id : decl.getTypeParams()) {
				sb.append(comma).append(id);
				comma = ",";
			}
			sb.append(">");
		}
		sb.append("(");
		String comma = "";
		for (VarList vl : decl.getInParams()) {
			sb.append(comma);
			if (vl.getIdentifiers().length > 0)
				sb.append(vl.getIdentifiers()[0]).append(":");
			appendType(sb, vl.getType(), 0);
			if (vl.getWhereClause() != null) {
				sb.append(" where ");
				appendExpression(sb, vl.getWhereClause(), 0);
			}
			comma = ", ";
		}
		sb.append(") returns (");
		comma = "";
		for (VarList vl : decl.getOutParams()) {
			sb.append(comma);
			if (vl.getIdentifiers().length > 0)
				sb.append(vl.getIdentifiers()[0]).append(":");
			appendType(sb, vl.getType(), 0);
			if (vl.getWhereClause() != null) {
				sb.append(" where ");
				appendExpression(sb, vl.getWhereClause(), 0);
			}
			comma = ", ";
		}
		sb.append(")");
		if (decl.getBody() == null)
			sb.append(";");
		writer.println(sb.toString());
		if (decl.getSpecification() != null) {
			for (Specification spec : decl.getSpecification())
				printSpecification(spec);
		}
		if (decl.getBody() != null) {
			writer.println("{");
			printBody(decl.getBody());
			writer.println("}");
		}
		writer.println();
	}

	private void printSpecification(Specification spec) {
		StringBuilder sb = new StringBuilder();
		sb.append("    ");
		if (spec.isFree())
			sb.append("free ");
		if (spec instanceof RequiresSpecification) {
			sb.append("requires ");
			appendExpression(sb, ((RequiresSpecification) spec).getFormula(), 0);
		} else if (spec instanceof EnsuresSpecification) {
			sb.append("ensures ");
			appendExpression(sb, ((EnsuresSpecification) spec).getFormula(), 0);
		} else if (spec instanceof ModifiesSpecification) {
			sb.append("modifies ");
			String comma = "";
			for (String id : ((ModifiesSpecification) spec).getIdentifiers()) {
				sb.append(comma).append(id);
				comma = ", ";
			}
		} else {
			throw new IllegalArgumentException(spec.toString());
		}
		sb.append(";");
		writer.println(sb.toString());
	}

	private void printBody(Body body) {
		for (VariableDeclaration decl : body.getLocalVars()) {
			printVarDeclaration(decl, "    ");
		}
		if (body.getLocalVars().length > 0)
			writer.println();
		printBlock(body.getBlock(), "");
	}

	private void printBlock(Statement[] block, String indent) {
		String nextIndent = indent + "    ";
		for (Statement s : block) {
			if (s instanceof Label) {
				// SF: Labels aren't on the first column anymore, they are
				// treated as pragmas if they are. Added "  "
				writer.println(indent + "  " + ((Label) s).getName() + ":");
			} else {
				printStatement(s, nextIndent);
			}
		}
	}

	private void printStatement(Statement s, String indent) {
		StringBuilder sb = new StringBuilder();
		sb.append(indent);
		if (s instanceof AssertStatement) {
			AssertStatement assertstmt = (AssertStatement) s;
			sb.append("assert ");
			appendExpression(sb, assertstmt.getFormula(), 0);
			sb.append(";");
			writer.println(sb.toString());
		} else if (s instanceof AssumeStatement) {
			AssumeStatement assumestmt = (AssumeStatement) s;
			sb.append("assume ");
			appendExpression(sb, assumestmt.getFormula(), 0);
			sb.append(";");
			writer.println(sb.toString());
		} else if (s instanceof HavocStatement) {
			HavocStatement havoc = (HavocStatement) s;
			sb.append("havoc ");
			String comma = "";
			for (String id : havoc.getIdentifiers()) {
				sb.append(comma).append(id);
				comma = ", ";
			}
			sb.append(";");
			writer.println(sb.toString());
		} else if (s instanceof AssignmentStatement) {
			AssignmentStatement stmt = (AssignmentStatement) s;
			String comma = "";
			for (LeftHandSide lhs : stmt.getLhs()) {
				sb.append(comma);
				appendLHS(sb, lhs);
				comma = ", ";
			}
			sb.append(" := ");
			comma = "";
			for (Expression rhs : stmt.getRhs()) {
				sb.append(comma);
				appendExpression(sb, rhs, 0);
				comma = ", ";
			}
			sb.append(";");
			writer.println(sb.toString());
		} else if (s instanceof CallStatement) {
			CallStatement call = (CallStatement) s;
			String comma;
			sb.append("call ");
			if (call.isForall())
				sb.append("forall ");
			if (call.getLhs().length > 0) {
				comma = "";
				for (String lhs : call.getLhs()) {
					sb.append(comma).append(lhs);
					comma = ", ";
				}
				sb.append(" := ");
			}
			sb.append(call.getMethodName());
			sb.append("(");
			comma = "";
			for (Expression arg : call.getArguments()) {
				sb.append(comma);
				appendExpression(sb, arg, 0);
				comma = ", ";
			}
			sb.append(");");
			writer.println(sb.toString());
		} else if (s instanceof IfStatement) {
			IfStatement stmt = (IfStatement) s;
			Statement[] elsePart;
			while (true) {
				sb.append("if (");
				appendExpression(sb, stmt.getCondition(), 0);
				sb.append(") {");
				writer.println(sb.toString());
				printBlock(stmt.getThenPart(), indent);
				sb = new StringBuilder();
				sb.append(indent).append("}");
				elsePart = stmt.getElsePart();
				if (elsePart.length != 1
						|| !(elsePart[0] instanceof IfStatement))
					break;
				stmt = (IfStatement) elsePart[0];
				sb.append(" else ");
			}
			if (elsePart.length > 0) {
				sb.append(" else {");
				writer.println(sb.toString());
				printBlock(stmt.getElsePart(), indent);
				sb = new StringBuilder();
				sb.append(indent).append("}");
			}
			writer.println(sb.toString());
		} else if (s instanceof WhileStatement) {
			WhileStatement stmt = (WhileStatement) s;
			sb.append("while (");
			appendExpression(sb, stmt.getCondition(), 0);
			sb.append(")");
			writer.println(sb.toString());
			for (LoopInvariantSpecification spec : stmt.getInvariants()) {
				sb = new StringBuilder();
				sb.append(indent).append("    ");
				if (spec.isFree()) {
					sb.append("free ");
				}
				sb.append("invariant ");
				appendExpression(sb, spec.getFormula(), 0);
				sb.append(";");
				writer.println(sb.toString());
			}
			sb = new StringBuilder();
			sb.append(indent).append("{");
			writer.println(sb.toString());
			printBlock(stmt.getBody(), indent);
			sb = new StringBuilder();
			sb.append(indent).append("}");
			writer.println(sb.toString());
		} else if (s instanceof BreakStatement) {
			String label = ((BreakStatement) s).getLabel();
			sb.append("break");
			if (label != null)
				sb.append(" ").append(label);
			sb.append(";");
			writer.println(sb.toString());
		} else if (s instanceof ReturnStatement) {
			sb.append("return;");
			writer.println(sb.toString());
		} else if (s instanceof GotoStatement) {
			sb.append("goto ");
			String comma = "";
			for (String label : ((GotoStatement) s).getLabels()) {
				sb.append(comma).append(label);
				comma = ", ";
			}
			sb.append(";");
			writer.println(sb.toString());
		} else {
			throw new IllegalArgumentException(s.toString());
		}
	}

	private void appendLHS(StringBuilder sb, LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			sb.append(((VariableLHS) lhs).getIdentifier());
		} else if (lhs instanceof ArrayLHS) {
			ArrayLHS arrlhs = (ArrayLHS) lhs;
			appendLHS(sb, arrlhs.getArray());
			sb.append("[");
			String comma = "";
			for (Expression index : arrlhs.getIndices()) {
				sb.append(comma);
				appendExpression(sb, index, 0);
				comma = ",";
			}
			sb.append("]");
		} else {
			throw new IllegalArgumentException(lhs.toString());
		}
	}

	private void printAxiom(Axiom decl) {
		StringBuilder sb = new StringBuilder();
		sb.append("axiom ");
		appendAttributes(sb, decl.getAttributes());
		appendExpression(sb, decl.getFormula(), 0);
		sb.append(";");
		writer.println(sb.toString());
	}

	private void printVarDeclaration(VariableDeclaration decl, String indent) {
		StringBuilder sb = new StringBuilder();
		sb.append(indent).append("var ");
		appendAttributes(sb, decl.getAttributes());
		String comma = "";
		for (VarList vl : decl.getVariables()) {
			sb.append(comma);
			comma = "";
			for (String id : vl.getIdentifiers()) {
				sb.append(comma).append(id);
				comma = ", ";
			}
			sb.append(" : ");
			appendType(sb, vl.getType(), 0);
			if (vl.getWhereClause() != null) {
				sb.append(" where ");
				appendExpression(sb, vl.getWhereClause(), 0);
			}
			comma = ", ";
		}
		sb.append(";");
		writer.println(sb.toString());
	}

	private void printConstDeclaration(ConstDeclaration decl) {
		StringBuilder sb = new StringBuilder();
		sb.append("const ");
		appendAttributes(sb, decl.getAttributes());
		if (decl.isUnique())
			sb.append("unique ");
		VarList vl = decl.getVarList();
		String comma = "";
		for (String id : vl.getIdentifiers()) {
			sb.append(comma).append(id);
			comma = ", ";
		}
		sb.append(" : ");
		appendType(sb, vl.getType(), 0);
		if (decl.getParentInfo() != null) {
			sb.append(" <:");
			comma = " ";
			for (ParentEdge edge : decl.getParentInfo()) {
				sb.append(comma);
				if (edge.isUnique())
					sb.append("unique ");
				sb.append(edge.getIdentifier());
				comma = ", ";
			}
		}
		if (decl.isComplete())
			sb.append(" complete");
		sb.append(";");
		writer.println(sb.toString());
	}

	// @Override
	public void finish() {

	}

	// @Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	// @Override
	public void init() {

	}

	@Override
	public boolean performedChanges() {
		return false;
	}

}
