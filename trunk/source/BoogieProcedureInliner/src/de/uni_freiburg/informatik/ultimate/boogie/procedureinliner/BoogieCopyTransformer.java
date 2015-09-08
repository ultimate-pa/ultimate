/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

/**
 * Modification of the BoogieTransformer,
 * which guarantees to return new instances for statements and expressions.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class BoogieCopyTransformer extends BoogieTransformer {
	
	
	protected Statement processStatement(Statement stat) {
		Statement newStat;
		if (stat instanceof AssertStatement) {
			Expression expr = ((AssertStatement) stat).getFormula();
			Expression newExpr = processExpression(expr);
			newStat = new AssertStatement(stat.getLocation(), newExpr);
		} else if (stat instanceof AssignmentStatement) {
			AssignmentStatement assign = (AssignmentStatement) stat;
			LeftHandSide[] lhs = assign.getLhs();
			LeftHandSide[] newLhs = processLeftHandSides(lhs);
			Expression[] rhs = assign.getRhs();
			Expression[] newRhs = processExpressions(rhs);
			newStat = new AssignmentStatement(stat.getLocation(), newLhs, newRhs);
		} else if (stat instanceof AssumeStatement) {
			Expression expr = ((AssumeStatement) stat).getFormula();
			Expression newExpr = processExpression(expr);
			newStat = new AssumeStatement(stat.getLocation(), newExpr);
		} else if (stat instanceof HavocStatement) {
			HavocStatement havoc = (HavocStatement) stat;
			VariableLHS[] ids = havoc.getIdentifiers();
			VariableLHS[] newIds = processVariableLHSs(ids);
			newStat = new HavocStatement(havoc.getLocation(), newIds);
		} else if (stat instanceof CallStatement) {
			CallStatement call = (CallStatement) stat;
			Expression[] args = call.getArguments();
			Expression[] newArgs = processExpressions(args);
			VariableLHS[] lhs = call.getLhs();
			VariableLHS[] newLhs = processVariableLHSs(lhs);
			newStat = new CallStatement(call.getLocation(), call.isForall(), newLhs, call.getMethodName(), newArgs);
		} else if (stat instanceof IfStatement) {
			IfStatement ifstmt = (IfStatement) stat;
			Expression cond = ifstmt.getCondition();
			Expression newCond = processExpression(cond);
			Statement[] thens = ifstmt.getThenPart();
			Statement[] newThens = processStatements(thens);
			Statement[] elses = ifstmt.getElsePart();
			Statement[] newElses = processStatements(elses);
			newStat = new IfStatement(ifstmt.getLocation(), newCond, newThens, newElses);
		} else if (stat instanceof WhileStatement) {
			WhileStatement whilestmt = (WhileStatement) stat;
			Expression cond = whilestmt.getCondition();
			Expression newCond = processExpression(cond);
			LoopInvariantSpecification[] invs = whilestmt.getInvariants();
			LoopInvariantSpecification[] newInvs = processLoopSpecifications(invs);
			Statement[] body = whilestmt.getBody();
			Statement[] newBody = processStatements(body);
			newStat = new WhileStatement(whilestmt.getLocation(), newCond, newInvs, newBody);
		} else if (stat instanceof BreakStatement) {
			BreakStatement bs = (BreakStatement) stat;
			newStat = new BreakStatement(bs.getLocation(), bs.getLabel());
		} else if (stat instanceof Label) {
			Label l = (Label) stat;
			newStat = new Label(l.getLocation(), l.getName());
		} else if (stat instanceof ReturnStatement) {
			ReturnStatement rs = (ReturnStatement) stat;
			newStat = new ReturnStatement(rs.getLocation());
		} else if (stat instanceof GotoStatement) {
			GotoStatement gs = (GotoStatement) stat;
			newStat = new GotoStatement(gs.getLocation(), gs.getLabels());
		} else {
			throw new UnsupportedOperationException("Cannot process unknown expression: " + stat.getClass().getName());
		}
		ModelUtils.mergeAnnotations(stat, newStat);
		return newStat;
	}

	protected Expression processExpression(Expression expr) {
		Expression newExpr;
		if (expr instanceof BinaryExpression) {
			BinaryExpression binexp = (BinaryExpression) expr;
			Expression left = processExpression(binexp.getLeft());
			Expression right = processExpression(binexp.getRight());
			newExpr = new BinaryExpression(expr.getLocation(), binexp.getType(), binexp.getOperator(), left, right);
		} else if (expr instanceof UnaryExpression) {
			UnaryExpression unexp = (UnaryExpression) expr;
			Expression subexpr = processExpression(unexp.getExpr());
			newExpr = new UnaryExpression(expr.getLocation(), unexp.getType(), unexp.getOperator(), subexpr);
		} else if (expr instanceof ArrayAccessExpression) {
			ArrayAccessExpression aaexpr = (ArrayAccessExpression) expr;
			Expression arr = processExpression(aaexpr.getArray());
			Expression[] indices = aaexpr.getIndices();
			Expression[] newIndices = processExpressions(indices);
			newExpr = new ArrayAccessExpression(aaexpr.getLocation(), aaexpr.getType(), arr, newIndices);
		} else if (expr instanceof ArrayStoreExpression) {
			ArrayStoreExpression aaexpr = (ArrayStoreExpression) expr;
			Expression arr = processExpression(aaexpr.getArray());
			Expression value = processExpression(aaexpr.getValue());
			Expression[] indices = aaexpr.getIndices();
			Expression[] newIndices = processExpressions(indices);
			newExpr = new ArrayStoreExpression(aaexpr.getLocation(), aaexpr.getType(), arr, newIndices, value);
		} else if (expr instanceof BitVectorAccessExpression) {
			BitVectorAccessExpression bvaexpr = (BitVectorAccessExpression) expr;
			Expression bv = processExpression(bvaexpr.getBitvec());
			newExpr = new BitVectorAccessExpression(bvaexpr.getLocation(), bvaexpr.getType(), bv, bvaexpr.getEnd(),
					bvaexpr.getStart());
		} else if (expr instanceof FunctionApplication) {
			FunctionApplication app = (FunctionApplication) expr;
			String name = app.getIdentifier();
			Expression[] args = processExpressions(app.getArguments());
			newExpr = new FunctionApplication(app.getLocation(), app.getType(), name, args);
		} else if (expr instanceof IfThenElseExpression) {
			IfThenElseExpression ite = (IfThenElseExpression) expr;
			Expression cond = processExpression(ite.getCondition());
			Expression thenPart = processExpression(ite.getThenPart());
			Expression elsePart = processExpression(ite.getElsePart());
			newExpr = new IfThenElseExpression(ite.getLocation(), thenPart.getType(), cond, thenPart, elsePart);
		} else if (expr instanceof QuantifierExpression) {
			QuantifierExpression quant = (QuantifierExpression) expr;
			Attribute[] attrs = quant.getAttributes();
			Attribute[] newAttrs = processAttributes(attrs);
			VarList[] params = quant.getParameters();
			VarList[] newParams = processVarLists(params);
			Expression subform = processExpression(quant.getSubformula());
			newExpr = new QuantifierExpression(quant.getLocation(), quant.getType(), quant.isUniversal(),
					quant.getTypeParams(), newParams, newAttrs, subform);
		} else if (expr instanceof StructConstructor) {
			StructConstructor sConst = (StructConstructor) expr;
			Expression[] fieldValues = processExpressions(sConst.getFieldValues());
			newExpr = new StructConstructor(sConst.getLocation(), sConst.getFieldIdentifiers(), fieldValues);
		} else if (expr instanceof StructAccessExpression) {
			StructAccessExpression sae = (StructAccessExpression) expr;
			Expression struct = processExpression(sae.getStruct());
			newExpr = new StructAccessExpression(sae.getLocation(), struct, sae.getField());
		} else if (expr instanceof BooleanLiteral) {
			BooleanLiteral bl = (BooleanLiteral) expr;
			newExpr = new BooleanLiteral(bl.getLocation(), bl.getType(),bl.getValue());
		} else if (expr instanceof IntegerLiteral) {
			IntegerLiteral il = (IntegerLiteral) expr;
			newExpr = new IntegerLiteral(il.getLocation(), il.getType(), il.getValue());
		} else if (expr instanceof BitvecLiteral) {
			BitvecLiteral bvl = (BitvecLiteral) expr;
			newExpr = new BitvecLiteral(bvl.getLocation(), bvl.getType(), bvl.getValue(), bvl.getLength());
		} else if (expr instanceof StringLiteral) {
			StringLiteral sl = (StringLiteral) expr;
			newExpr = new StringLiteral(sl.getLocation(), sl.getType(), sl.getValue());
		} else if (expr instanceof IdentifierExpression) {
			IdentifierExpression ie = (IdentifierExpression) expr;
			newExpr = new IdentifierExpression(ie.getLocation(), ie.getType(), ie.getIdentifier(),
					ie.getDeclarationInformation());
		} else if (expr instanceof WildcardExpression) {
			WildcardExpression we = (WildcardExpression) expr;
			newExpr = new WildcardExpression(we.getLocation(), we.getType());
		} else if (expr instanceof RealLiteral) {
			RealLiteral rl = (RealLiteral) expr;
			newExpr = new RealLiteral(rl.getLocation(), rl.getType(), rl.getValue());
		} else {
			throw new UnsupportedOperationException("Cannot process unknown expression: " + expr.getClass().getName());
		}
		ModelUtils.mergeAnnotations(expr, newExpr);
		return newExpr;
	}
}
