package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.NameHandler.Boogie2C;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;

/**
 * Translation from Boogie to C for traces and expressions.
 */
public class Backtranslator extends DefaultTranslator<ASTNode, CACSLLocation, Expression, String> {

	Map<ASTNode, CACSLLocation> m_Position = 
			new HashMap<ASTNode, CACSLLocation>();
	Boogie2C m_boogie2C;

	public Backtranslator() {
	}
	
	@Override
	public List<CACSLLocation> translateTrace(List<ASTNode> trace) {
		// TODO Auto-generated method stub
		return super.translateTrace(trace);
	}
	
	
//	protected Expression[] processExpressions(Expression[] exprs) {
//		Expression[] newExprs = new Expression[exprs.length];
//		boolean changed = false;
//		for (int j = 0; j < exprs.length; j++) {
//			newExprs[j] = processExpression(exprs[j]);
//			if (newExprs[j] != exprs[j])
//				changed = true;
//		}
//		return changed ? newExprs : exprs;
//	}

	@Override
	public String translateExpression(Expression expression) {
		String result;
		try {
			result = processExpression(expression);
		} catch (UnsupportedOperationException e) {
			result = "Backtranslation of expression failed " + e.toString();
		}
		return result;

	}
	
	public void setBoogie2C(Boogie2C boogie2c) {
		m_boogie2C = boogie2c;
	}
	
	
	private String translateBinExpOp(BinaryExpression.Operator op) {
		switch (op) {
		case ARITHDIV: return "/";
		case ARITHMINUS: return "-";
		case ARITHMOD: return "%";
		case ARITHMUL: return "*";
		case ARITHPLUS: return "+";
		case BITVECCONCAT: throw new UnsupportedOperationException("Unsupported BITVECCONCAT");
		case COMPEQ: return "==";
		case COMPGEQ: return ">=";
		case COMPGT: return ">";
		case COMPLEQ: return "<=";
		case COMPLT: return "<";
		case COMPNEQ: return "!=";
		case COMPPO: throw new UnsupportedOperationException("Unsupported COMPPO");
		case LOGICAND: return "&&";
		case LOGICIFF: return "<==>";
		case LOGICIMPLIES: return "==>";
		case LOGICOR: return "||";
		default:
			throw new UnsupportedOperationException("Unknown binary operator");
		}
	}
		
	private String translateUnExpOp(UnaryExpression.Operator op) {
		switch (op) {
		case ARITHNEGATIVE: return "-";
		case LOGICNEG: return "!";
		case OLD: return "\\old";
		default:
			throw new UnsupportedOperationException("Unknown unary operator");
		}
	}
	
	private String translateIdentifierExpression(IdentifierExpression expr) {
		final String boogieId = ((IdentifierExpression) expr).getIdentifier();
		final String cId;
		if (boogieId.equals(SFO.RES)) {
			cId = "\\result";
		} else if (m_boogie2C.getVar2cvar().containsKey(boogieId)) {
			cId = m_boogie2C.getVar2cvar().get(boogieId);			
		} else if (m_boogie2C.getInvar2cvar().containsKey(boogieId)) {
			cId = "\\old(" + m_boogie2C.getInvar2cvar().get(boogieId) + ")";
		} else if (m_boogie2C.getTempvar2obj().containsKey(boogieId)) {
			throw new UnsupportedOperationException(
					"auxilliary boogie variable " + boogieId);
		} else if (boogieId.equals(SFO.VALID)) {
			cId = "\\valid";	
		} else {
			throw new UnsupportedOperationException("unknown boogie variable " + boogieId);
		}
		return cId;
	}
	

	private String processExpression(Expression expr) {
		if (expr instanceof BinaryExpression) {
			BinaryExpression binexp = (BinaryExpression) expr;
			String left = processExpression(binexp.getLeft());
			String right = processExpression(binexp.getRight());
			if (binexp.getOperator() == BinaryExpression.Operator.LOGICAND) {
				return left + " " + translateBinExpOp(binexp.getOperator()) + " " + right;
			} else {
				return "(" + left + translateBinExpOp(binexp.getOperator()) + right + ")";
			}
		} else if (expr instanceof UnaryExpression) {
			UnaryExpression unexp = (UnaryExpression) expr;
			String subexpr = processExpression(unexp.getExpr());
			String operator = translateUnExpOp(unexp.getOperator());
			if (unexp.getOperator().equals(UnaryExpression.Operator.OLD)) {
				return operator + "(" + subexpr + ")";
			} else if (unexp.getOperator().equals(UnaryExpression.Operator.LOGICNEG)) {
				if (!subexpr.startsWith("(")) {
					subexpr = "(" + subexpr + ")";
				}
				return operator + subexpr;
			} else if (unexp.getOperator().equals(UnaryExpression.Operator.ARITHNEGATIVE)) {
				return operator + subexpr;
			} else {
				throw new IllegalArgumentException("unknown unary operator");
			}
		} else if (expr instanceof ArrayAccessExpression) {
			throw new UnsupportedOperationException("Unsupported ArrayAccessExpression");
		} else if (expr instanceof ArrayStoreExpression) {
			throw new UnsupportedOperationException("Unsupported ArrayStoreExpression");
		} else if (expr instanceof BitVectorAccessExpression) {
			throw new UnsupportedOperationException("Unsupported BitVectorAccessExpression");
		} else if (expr instanceof FunctionApplication) {
			throw new UnsupportedOperationException("Unsupported FunctionApplication");
		} else if (expr instanceof IfThenElseExpression) {
			IfThenElseExpression ite = (IfThenElseExpression) expr;
			String cond = processExpression(ite.getCondition());
			String thenPart = processExpression(ite.getThenPart());
			String elsePart = processExpression(ite.getElsePart());
			return "(" + cond + " ? " + thenPart + " : " + elsePart + ")"; 
		} else if (expr instanceof QuantifierExpression) {
			throw new UnsupportedOperationException("Unsupported QuantifierExpression");
		} else if (expr instanceof IdentifierExpression) {
			return translateIdentifierExpression((IdentifierExpression) expr);
		} else if (expr instanceof IntegerLiteral) {
			IntegerLiteral intLit = (IntegerLiteral) expr;
			return intLit.getValue();
		} else if (expr instanceof BooleanLiteral) {
			BooleanLiteral boolLit = (BooleanLiteral) expr;
			if (boolLit.getValue()) {
				return "\\true";
			} else {
				return "\\false";
			}
		} else if (expr instanceof RealLiteral) {
			RealLiteral realLit = (RealLiteral) expr;
			return realLit.getValue();
		}
		throw new UnsupportedOperationException("Unknown Expression");
	}


	
	

}
