package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;

public class WeakestPrecondition extends BoogieTransformer {
	
	HashMap<String, Expression> name2expression = 
											new HashMap<String,Expression>();
	Expression m_Result;
	
	public WeakestPrecondition(Expression expr, CallStatement call, Procedure proc) {
		Expression[] arguments = call.getArguments();
		VarList[] inParams = proc.getInParams();
		int paramNumber = 0;
		for (VarList varList : inParams) {
			String[] identifiers = varList.getIdentifiers();
			for (String identifier : identifiers) {
				if (paramNumber>= arguments.length) {
					throw new IllegalArgumentException("CallStatement" + call + 
					"has wrong number of arguments");
				}
				name2expression.put(identifier, arguments[paramNumber]);
				paramNumber++;
			}
		}
		if (arguments.length!=paramNumber) {
			throw new IllegalArgumentException("CallStatement" + call + 
					"has wrong number of arguments");
		}
		
		m_Result = processExpression(expr);
	}
	
	@Override
	protected Expression processExpression(Expression expr) {
		if (expr instanceof IdentifierExpression) {
			IdentifierExpression iExpr = (IdentifierExpression) expr;
			Expression substitute = name2expression.get(iExpr.getIdentifier());
			if (substitute == null) {
				return expr;
			}
			else {
				return substitute;
			}
		}
		else if (expr instanceof UnaryExpression) {
			UnaryExpression unexp = (UnaryExpression) expr;
			if (unexp.getOperator() == Operator.OLD) {
				return unexp.getExpr();
			}
			else {
				Expression subexpr = processExpression(unexp.getExpr());
				if (subexpr != unexp.getExpr()) {
					return new UnaryExpression(subexpr.getLocation(), unexp.getType(),
							unexp.getOperator(), subexpr);
				}

			}
		}
		// from here on: copy&paste from superclass method
		else if (expr instanceof BinaryExpression) {
			BinaryExpression binexp = (BinaryExpression) expr;
			Expression left = processExpression(binexp.getLeft());
			Expression right = processExpression(binexp.getRight());
			if (left != binexp.getLeft()
				|| right != binexp.getRight()) {
				return new BinaryExpression(expr.getLocation(), binexp.getType(),
						binexp.getOperator(), left, right);
			}
		} else if (expr instanceof UnaryExpression) {
			UnaryExpression unexp = (UnaryExpression) expr;
			Expression subexpr = processExpression(unexp.getExpr());
			if (subexpr != unexp.getExpr()) {
				return new UnaryExpression(expr.getLocation(), unexp.getType(),
						unexp.getOperator(), subexpr);
			}
		} else if (expr instanceof ArrayAccessExpression) {
			ArrayAccessExpression aaexpr = (ArrayAccessExpression) expr;
			Expression arr = processExpression(aaexpr.getArray());
			boolean changed = arr != aaexpr.getArray();
			Expression[] indices = aaexpr.getIndices();
			Expression[] newIndices = new Expression[indices.length];
			for (int i = 0; i < indices.length; i++) {
				newIndices[i] = processExpression(indices[i]);
				if (newIndices[i] != indices[i])
					changed = true;
			}
			if (changed)
				return new ArrayAccessExpression(expr.getLocation(), aaexpr.getType(), arr, newIndices);
		} else if (expr instanceof ArrayStoreExpression) {
			ArrayStoreExpression aaexpr = (ArrayStoreExpression) expr;
			Expression arr = processExpression(aaexpr.getArray());
			Expression value = processExpression(aaexpr.getValue());
			boolean changed = arr != aaexpr.getArray() || value != aaexpr.getValue();
			Expression[] indices = aaexpr.getIndices();
			Expression[] newIndices = new Expression[indices.length];
			for (int i = 0; i < indices.length; i++) {
				newIndices[i] = processExpression(indices[i]);
				if (newIndices[i] != indices[i])
					changed = true;
			}
			if (changed)
				return new ArrayStoreExpression(expr.getLocation(), aaexpr.getType(), arr, newIndices, value);
		} else if (expr instanceof BitVectorAccessExpression) {
			BitVectorAccessExpression bvaexpr = 
				(BitVectorAccessExpression) expr;
			Expression bv = processExpression(bvaexpr.getBitvec());
			if (bv != bvaexpr.getBitvec())
				return new BitVectorAccessExpression(expr.getLocation(), bvaexpr.getType(), bv, 
						bvaexpr.getEnd(), bvaexpr.getStart());
		} else if (expr instanceof FunctionApplication) {
			FunctionApplication app = (FunctionApplication) expr;
			String name = app.getIdentifier();
			Expression[] args = processExpressions(app.getArguments());
			if (args != app.getArguments())
				return new FunctionApplication(expr.getLocation(), app.getType(), name, args);
		} else if (expr instanceof IfThenElseExpression) {
			IfThenElseExpression ite = (IfThenElseExpression) expr;
			Expression cond = processExpression(ite.getCondition());
			Expression thenPart = processExpression(ite.getThenPart());
			Expression elsePart = processExpression(ite.getElsePart());
			if (cond != ite.getCondition()
			    || thenPart != ite.getThenPart()
			    || elsePart != ite.getElsePart())
				return new IfThenElseExpression(expr.getLocation(), ite.getType(), cond, thenPart, elsePart);
		} else if (expr instanceof QuantifierExpression) {
			QuantifierExpression quant = (QuantifierExpression) expr;
			Attribute[] attrs = quant.getAttributes();
			Attribute[] newAttrs = processAttributes(attrs);
			VarList[] params = quant.getParameters();
			VarList[] newParams = processVarLists(params);
			Expression subform = processExpression(quant.getSubformula());
			if (subform != quant.getSubformula()
				|| attrs != newAttrs
				|| params != newParams)
				return new QuantifierExpression(expr.getLocation(), quant.getType(), quant.isUniversal(), 
						quant.getTypeParams(), newParams, newAttrs, subform);
		}
		return expr;
	}
	
	public Expression getResult() {
		return m_Result;
	}

}
