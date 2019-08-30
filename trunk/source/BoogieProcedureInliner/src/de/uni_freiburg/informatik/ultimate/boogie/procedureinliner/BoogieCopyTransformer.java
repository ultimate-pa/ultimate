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

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;

/**
 * Modification of the BoogieTransformer, which guarantees to return new instances for statements and expressions.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class BoogieCopyTransformer extends BoogieTransformer {

	@Override
	protected Statement processStatement(final Statement stat) {
		Statement newStat;
		if (stat instanceof AssertStatement) {
			final AssertStatement assertStmt = (AssertStatement) stat;
			final Expression expr = assertStmt.getFormula();
			final Expression newExpr = processExpression(expr);
			final Attribute[] newAttr = processAttributes(assertStmt.getAttributes());
			newStat = new AssertStatement(stat.getLocation(), (NamedAttribute[]) newAttr, newExpr);
		} else if (stat instanceof AssignmentStatement) {
			final AssignmentStatement assign = (AssignmentStatement) stat;
			final LeftHandSide[] lhs = assign.getLhs();
			final LeftHandSide[] newLhs = processLeftHandSides(lhs);
			final Expression[] rhs = assign.getRhs();
			final Expression[] newRhs = processExpressions(rhs);
			newStat = new AssignmentStatement(stat.getLocation(), newLhs, newRhs);
		} else if (stat instanceof AssumeStatement) {
			final AssumeStatement assumeStmt = (AssumeStatement) stat;
			final Expression expr = assumeStmt.getFormula();
			final Expression newExpr = processExpression(expr);
			final Attribute[] newAttr = processAttributes(assumeStmt.getAttributes());
			newStat = new AssumeStatement(stat.getLocation(), (NamedAttribute[]) newAttr, newExpr);
		} else if (stat instanceof HavocStatement) {
			final HavocStatement havoc = (HavocStatement) stat;
			final VariableLHS[] ids = havoc.getIdentifiers();
			final VariableLHS[] newIds = processVariableLHSs(ids);
			newStat = new HavocStatement(havoc.getLocation(), newIds);
		} else if (stat instanceof CallStatement) {
			final CallStatement call = (CallStatement) stat;
			final Expression[] args = call.getArguments();
			final Expression[] newArgs = processExpressions(args);
			final VariableLHS[] lhs = call.getLhs();
			final VariableLHS[] newLhs = processVariableLHSs(lhs);
			newStat = new CallStatement(call.getLocation(), call.getAttributes(), call.isForall(), newLhs,
					call.getMethodName(), newArgs);
		} else if (stat instanceof IfStatement) {
			final IfStatement ifstmt = (IfStatement) stat;
			final Expression cond = ifstmt.getCondition();
			final Expression newCond = processExpression(cond);
			final Statement[] thens = ifstmt.getThenPart();
			final Statement[] newThens = processStatements(thens);
			final Statement[] elses = ifstmt.getElsePart();
			final Statement[] newElses = processStatements(elses);
			newStat = new IfStatement(ifstmt.getLocation(), newCond, newThens, newElses);
		} else if (stat instanceof WhileStatement) {
			final WhileStatement whilestmt = (WhileStatement) stat;
			final Expression cond = whilestmt.getCondition();
			final Expression newCond = processExpression(cond);
			final LoopInvariantSpecification[] invs = whilestmt.getInvariants();
			final LoopInvariantSpecification[] newInvs = processLoopSpecifications(invs);
			final Statement[] body = whilestmt.getBody();
			final Statement[] newBody = processStatements(body);
			newStat = new WhileStatement(whilestmt.getLocation(), newCond, newInvs, newBody);
		} else if (stat instanceof AtomicStatement) {
			final AtomicStatement atomicstmt = (AtomicStatement) stat;
			final Statement[] body = atomicstmt.getBody();
			final Statement[] newBody = processStatements(body);
			newStat = new AtomicStatement(atomicstmt.getLocation(), newBody);
		} else if (stat instanceof BreakStatement) {
			final BreakStatement bs = (BreakStatement) stat;
			newStat = new BreakStatement(bs.getLocation(), bs.getLabel());
		} else if (stat instanceof Label) {
			final Label l = (Label) stat;
			newStat = new Label(l.getLocation(), l.getName());
		} else if (stat instanceof ReturnStatement) {
			final ReturnStatement rs = (ReturnStatement) stat;
			newStat = new ReturnStatement(rs.getLocation());
		} else if (stat instanceof GotoStatement) {
			final GotoStatement gs = (GotoStatement) stat;
			newStat = new GotoStatement(gs.getLocation(), gs.getLabels());
		} else if (stat instanceof ForkStatement) {
			final ForkStatement forkstmt = (ForkStatement) stat;
			final Expression[] threadId = forkstmt.getThreadID();
			final String procName = forkstmt.getProcedureName();
			final Expression[] arguments = forkstmt.getArguments();
			final Expression[] newThreadId = processExpressions(threadId);
			final Expression[] newArguments = processExpressions(arguments);
			newStat = new ForkStatement(forkstmt.getLoc(), newThreadId, procName, newArguments);
		} else if (stat instanceof JoinStatement) {
			final JoinStatement joinstmt = (JoinStatement) stat;
			final Expression[] threadId = joinstmt.getThreadID();
			final VariableLHS[] lhs = joinstmt.getLhs();
			final Expression[] newThreadId = processExpressions(threadId);
			final VariableLHS[] newLhs = processVariableLHSs(lhs);
			newStat = new JoinStatement(joinstmt.getLoc(), newThreadId, newLhs);
		} else {
			throw new UnsupportedOperationException("Cannot process unknown expression: " + stat.getClass().getName());
		}
		ModelUtils.copyAnnotations(stat, newStat);
		return newStat;
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		Expression newExpr;
		if (expr instanceof BinaryExpression) {
			final BinaryExpression binexp = (BinaryExpression) expr;
			final Expression left = processExpression(binexp.getLeft());
			final Expression right = processExpression(binexp.getRight());
			newExpr = new BinaryExpression(expr.getLocation(), binexp.getType(), binexp.getOperator(), left, right);
		} else if (expr instanceof UnaryExpression) {
			final UnaryExpression unexp = (UnaryExpression) expr;
			final Expression subexpr = processExpression(unexp.getExpr());
			newExpr = new UnaryExpression(expr.getLocation(), unexp.getType(), unexp.getOperator(), subexpr);
		} else if (expr instanceof ArrayAccessExpression) {
			final ArrayAccessExpression aaexpr = (ArrayAccessExpression) expr;
			final Expression arr = processExpression(aaexpr.getArray());
			final Expression[] indices = aaexpr.getIndices();
			final Expression[] newIndices = processExpressions(indices);
			newExpr = new ArrayAccessExpression(aaexpr.getLocation(), aaexpr.getType(), arr, newIndices);
		} else if (expr instanceof ArrayStoreExpression) {
			final ArrayStoreExpression aaexpr = (ArrayStoreExpression) expr;
			final Expression arr = processExpression(aaexpr.getArray());
			final Expression value = processExpression(aaexpr.getValue());
			final Expression[] indices = aaexpr.getIndices();
			final Expression[] newIndices = processExpressions(indices);
			newExpr = new ArrayStoreExpression(aaexpr.getLocation(), aaexpr.getType(), arr, newIndices, value);
		} else if (expr instanceof BitVectorAccessExpression) {
			final BitVectorAccessExpression bvaexpr = (BitVectorAccessExpression) expr;
			final Expression bv = processExpression(bvaexpr.getBitvec());
			newExpr = new BitVectorAccessExpression(bvaexpr.getLocation(), bvaexpr.getType(), bv, bvaexpr.getEnd(),
					bvaexpr.getStart());
		} else if (expr instanceof FunctionApplication) {
			final FunctionApplication app = (FunctionApplication) expr;
			final String name = app.getIdentifier();
			final Expression[] args = processExpressions(app.getArguments());
			newExpr = new FunctionApplication(app.getLocation(), app.getType(), name, args);
		} else if (expr instanceof IfThenElseExpression) {
			final IfThenElseExpression ite = (IfThenElseExpression) expr;
			final Expression cond = processExpression(ite.getCondition());
			final Expression thenPart = processExpression(ite.getThenPart());
			final Expression elsePart = processExpression(ite.getElsePart());
			newExpr = new IfThenElseExpression(ite.getLocation(), thenPart.getType(), cond, thenPart, elsePart);
		} else if (expr instanceof QuantifierExpression) {
			final QuantifierExpression quant = (QuantifierExpression) expr;
			final Attribute[] attrs = quant.getAttributes();
			final Attribute[] newAttrs = processAttributes(attrs);
			final VarList[] params = quant.getParameters();
			final VarList[] newParams = processVarLists(params);
			final Expression subform = processExpression(quant.getSubformula());
			newExpr = new QuantifierExpression(quant.getLocation(), quant.getType(), quant.isUniversal(),
					quant.getTypeParams(), newParams, newAttrs, subform);
		} else if (expr instanceof StructConstructor) {
			final StructConstructor sConst = (StructConstructor) expr;
			final Expression[] fieldValues = processExpressions(sConst.getFieldValues());
			newExpr = new StructConstructor(sConst.getLocation(), sConst.getFieldIdentifiers(), fieldValues);
		} else if (expr instanceof StructAccessExpression) {
			final StructAccessExpression sae = (StructAccessExpression) expr;
			final Expression struct = processExpression(sae.getStruct());
			newExpr = new StructAccessExpression(sae.getLocation(), struct, sae.getField());
		} else if (expr instanceof BooleanLiteral) {
			final BooleanLiteral bl = (BooleanLiteral) expr;
			newExpr = new BooleanLiteral(bl.getLocation(), bl.getType(), bl.getValue());
		} else if (expr instanceof IntegerLiteral) {
			final IntegerLiteral il = (IntegerLiteral) expr;
			newExpr = new IntegerLiteral(il.getLocation(), il.getType(), il.getValue());
		} else if (expr instanceof BitvecLiteral) {
			final BitvecLiteral bvl = (BitvecLiteral) expr;
			newExpr = new BitvecLiteral(bvl.getLocation(), bvl.getType(), bvl.getValue(), bvl.getLength());
		} else if (expr instanceof StringLiteral) {
			final StringLiteral sl = (StringLiteral) expr;
			newExpr = new StringLiteral(sl.getLocation(), sl.getType(), sl.getValue());
		} else if (expr instanceof IdentifierExpression) {
			final IdentifierExpression ie = (IdentifierExpression) expr;
			newExpr = new IdentifierExpression(ie.getLocation(), ie.getType(), ie.getIdentifier(),
					ie.getDeclarationInformation());
		} else if (expr instanceof WildcardExpression) {
			final WildcardExpression we = (WildcardExpression) expr;
			newExpr = new WildcardExpression(we.getLocation(), we.getType());
		} else if (expr instanceof RealLiteral) {
			final RealLiteral rl = (RealLiteral) expr;
			newExpr = new RealLiteral(rl.getLocation(), rl.getType(), rl.getValue());
		} else {
			throw new UnsupportedOperationException("Cannot process unknown expression: " + expr.getClass().getName());
		}
		ModelUtils.copyAnnotations(expr, newExpr);
		return newExpr;
	}
}
