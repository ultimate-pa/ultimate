package local.stalin.plugins.generator.rcfgbuilder;

import local.stalin.model.boogie.ast.ASTType;
import local.stalin.model.boogie.ast.ArrayAccessExpression;
import local.stalin.model.boogie.ast.ArrayLHS;
import local.stalin.model.boogie.ast.ArrayStoreExpression;
import local.stalin.model.boogie.ast.ArrayType;
import local.stalin.model.boogie.ast.AssertStatement;
import local.stalin.model.boogie.ast.AssignmentStatement;
import local.stalin.model.boogie.ast.AssumeStatement;
import local.stalin.model.boogie.ast.Attribute;
import local.stalin.model.boogie.ast.BinaryExpression;
import local.stalin.model.boogie.ast.BitVectorAccessExpression;
import local.stalin.model.boogie.ast.BitvecLiteral;
import local.stalin.model.boogie.ast.BooleanLiteral;
import local.stalin.model.boogie.ast.CallStatement;
import local.stalin.model.boogie.ast.Expression;
import local.stalin.model.boogie.ast.FunctionApplication;
import local.stalin.model.boogie.ast.HavocStatement;
import local.stalin.model.boogie.ast.IdentifierExpression;
import local.stalin.model.boogie.ast.IfThenElseExpression;
import local.stalin.model.boogie.ast.IntegerLiteral;
import local.stalin.model.boogie.ast.LeftHandSide;
import local.stalin.model.boogie.ast.NamedAttribute;
import local.stalin.model.boogie.ast.NamedType;
import local.stalin.model.boogie.ast.PrimitiveType;
import local.stalin.model.boogie.ast.QuantifierExpression;
import local.stalin.model.boogie.ast.RealLiteral;
import local.stalin.model.boogie.ast.ReturnStatement;
import local.stalin.model.boogie.ast.Statement;
import local.stalin.model.boogie.ast.StringLiteral;
import local.stalin.model.boogie.ast.Trigger;
import local.stalin.model.boogie.ast.UnaryExpression;
import local.stalin.model.boogie.ast.VarList;
import local.stalin.model.boogie.ast.VariableLHS;
import local.stalin.model.boogie.ast.WildcardExpression;

/**
 * Provides a static method to get a prettyprinted String representation of a
 * (Boogie) Statement.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */

public class BoogieStatementPrettyPrinter {
	
	/**
	 * @return prettyprinted String representation the Statement st
	 */
	public static String print(Statement st) {
		return printStatement(st, "");
	}

	// Aus Jochens BoogiePrinter Observer	
	private static String printStatement(Statement s, String indent) {
		StringBuilder sb = new StringBuilder();
		sb.append(indent);
		if (s instanceof AssertStatement) {
			AssertStatement assertstmt = (AssertStatement) s;
			sb.append("assert ");
			appendExpression(sb, assertstmt.getFormula(), 0);
			sb.append(";");
			return sb.toString();
		} else if (s instanceof AssumeStatement) {
			AssumeStatement assumestmt = (AssumeStatement) s;
			sb.append("assume ");
			appendExpression(sb, assumestmt.getFormula(), 0);
			sb.append(";");
			return sb.toString();
		} else if (s instanceof HavocStatement) {
			HavocStatement havoc = (HavocStatement) s;
			sb.append("havoc ");
			String comma = "";
			for (String id: havoc.getIdentifiers()) {
				sb.append(comma).append(id);
				comma = ", ";
			}
			sb.append(";");
			return sb.toString();
		} else if (s instanceof AssignmentStatement) {
			AssignmentStatement stmt = (AssignmentStatement) s;
			String comma = "";
			for (LeftHandSide lhs: stmt.getLhs()) {
				sb.append(comma);
				appendLHS(sb, lhs);
				comma = ", ";
			}
			sb.append(" := ");
			comma = "";
			for (Expression rhs: stmt.getRhs()) {
				sb.append(comma);
				appendExpression(sb, rhs, 0);
				comma = ", ";
			}
			sb.append(";");
			return sb.toString();
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
			for (Expression arg: call.getArguments()) {
				sb.append(comma);
				appendExpression(sb, arg, 0);
				comma = ", ";
			}
			sb.append(");");
			return sb.toString();
		} else if (s instanceof ReturnStatement) {
			sb.append("return;");
			return sb.toString();
		} else {
			throw new IllegalArgumentException(s.toString());
		}
	}





	private static void appendExpression(StringBuilder sb, Expression expr,
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



	private static void appendType(StringBuilder sb, ASTType type, int precedence) {
		if (type instanceof NamedType) {
			NamedType nt = (NamedType) type;
			ASTType[] args = nt.getTypeArgs();

			if (precedence > 0 && args.length > 0)
				sb.append("(");
			sb.append(nt.getName());
			for (int i = 0; i < args.length; i++) {
				sb.append(" ");
				appendType(sb, args[i], i < args.length-1 ? 2 : 1);
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
			for (ASTType indexType: at.getIndexTypes()) {
				sb.append(comma);
				appendType(sb, indexType, 0);
				comma = ",";
			}
			sb.append("]");
			appendType(sb, at.getValueType(), 0);
			if (precedence > 1)
				sb.append(")");
		} else if (type instanceof PrimitiveType) {
			sb.append(((PrimitiveType)type).getName());
		}
	}

	private static void appendAttributes(StringBuilder sb, Attribute[] attributes) {
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
				for (Expression value : ((Trigger)a).getTriggers()) {
					sb.append(comma);
					appendExpression(sb, value, 0);
					comma = ",";
				}
				sb.append(" } ");
			}
		}
	}


	private static void appendLHS(StringBuilder sb, LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			sb.append(((VariableLHS)lhs).getIdentifier());
		} else if (lhs instanceof ArrayLHS) {
			ArrayLHS arrlhs = (ArrayLHS) lhs;
			appendLHS(sb, arrlhs.getArray());
			sb.append("[");
			String comma = "";
			for (Expression index: arrlhs.getIndices()) {
				sb.append(comma);
				appendExpression(sb, index, 0);
				comma = ",";
			}
			sb.append("]");
		} else {
			throw new IllegalArgumentException(lhs.toString());
		}
	}
}
