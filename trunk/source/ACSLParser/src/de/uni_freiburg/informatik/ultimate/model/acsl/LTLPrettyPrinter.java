package de.uni_freiburg.informatik.ultimate.model.acsl;

import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLVisitor;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression.Operator;

/**
 * Preliminary ACSL LTL extension pretty printer
 * 
 * @author dietsch@informatik.uni-freiburg.de
 */
public class LTLPrettyPrinter extends ACSLVisitor {

	private StringBuilder mBuilder;

	public String print(ACSLNode node) {
		mBuilder = new StringBuilder();
		node.accept(this);
		return mBuilder.toString();
	}

	@Override
	public boolean visit(BinaryExpression node) {
		mBuilder.append("(");
		node.getLeft().accept(this);
		mBuilder.append(" ");
		mBuilder.append(getString(node.getOperator()));
		mBuilder.append(" ");
		node.getRight().accept(this);
		mBuilder.append(")");
		return false;
	}

	@Override
	public boolean visit(UnaryExpression node) {
		mBuilder.append(getString(node.getOperator()));
		mBuilder.append("(");
		node.getExpr().accept(this);
		mBuilder.append(")");
		return false;
	}

	@Override
	public boolean visit(BooleanLiteral node) {
		mBuilder.append(node.getValue());
		return super.visit(node);
	}

	@Override
	public boolean visit(IdentifierExpression node) {
		mBuilder.append(node.getIdentifier());
		return super.visit(node);
	}

	@Override
	public boolean visit(IntegerLiteral node) {
		mBuilder.append(node.getValue());
		return super.visit(node);
	}

	@Override
	public boolean visit(RealLiteral node) {
		mBuilder.append(node.getValue());
		return super.visit(node);
	}

	private String getString(UnaryExpression.Operator operator) {
		switch (operator) {
		case ADDROF:
			return "&";
		case LOGICNEG:
			return "!";
		case LTLFINALLY:
			return "F";
		case LTLGLOBALLY:
			return "G";
		case LTLNEXT:
			return "X";
		case MINUS:
			return "-";
		case PLUS:
			return "+";
		case POINTER:
			return "*";
		case LOGICCOMPLEMENT:
		default:
			throw new UnsupportedOperationException("getString(" + operator + ") not implemented");
		}
	}

	private String getString(Operator operator) {
		switch (operator) {
		case ARITHDIV:
			return "/";
		case ARITHMINUS:
			return "-";
		case ARITHMOD:
			return "%";
		case ARITHMUL:
			return "*";
		case ARITHPLUS:
			return "+";
		case BITAND:
			return "&";
		case BITIFF:
			return "<-->";
		case BITIMPLIES:
			return "-->";
		case BITOR:
			return "|";
		case COMPEQ:
			return "==";
		case COMPGEQ:
			return ">=";
		case COMPGT:
			return ">";
		case COMPLEQ:
			return "<=";
		case COMPLT:
			return "<";
		case COMPNEQ:
			return "!=";
		case LOGICAND:
			return "&&";
		case LOGICIFF:
			return "<==>";
		case LOGICIMPLIES:
			return "==>";
		case LOGICOR:
			return "||";
		case LTLUNTIL:
			return "U";
		case LTLRELEASE:
			return "R";
		case LTLWEAKUNTIL:
			return "WU";
		case LOGICXOR:
		case COMPPO:
		case BITXOR:
		case BITVECCONCAT:
		default:
			throw new UnsupportedOperationException("getString(" + operator + ") not implemented");
		}
	}

}