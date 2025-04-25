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
		final Statement newStat = switch (stat) {
		case final AssertStatement assertStmt -> {
			final Expression newExpr = processExpression(assertStmt.getFormula());
			final Attribute[] newAttr = processAttributes(assertStmt.getAttributes());
			yield new AssertStatement(stat.getLocation(), (NamedAttribute[]) newAttr, newExpr);
		}
		case final AssignmentStatement assign -> {
			final LeftHandSide[] newLhs = processLeftHandSides(assign.getLhs());
			final Expression[] newRhs = processExpressions(assign.getRhs());
			yield new AssignmentStatement(stat.getLocation(), newLhs, newRhs);
		}
		case final AssumeStatement assumeStmt -> {
			final Expression newExpr = processExpression(assumeStmt.getFormula());
			final Attribute[] newAttr = processAttributes(assumeStmt.getAttributes());
			yield new AssumeStatement(stat.getLocation(), (NamedAttribute[]) newAttr, newExpr);
		}
		case final HavocStatement havoc -> {
			final VariableLHS[] newIds = processVariableLHSs(havoc.getIdentifiers());
			yield new HavocStatement(havoc.getLocation(), newIds);
		}
		case final CallStatement call -> {
			final Expression[] newArgs = processExpressions(call.getArguments());
			final VariableLHS[] newLhs = processVariableLHSs(call.getLhs());
			yield new CallStatement(call.getLocation(), call.getAttributes(), call.isForall(), newLhs,
					call.getMethodName(), newArgs);
		}
		case final IfStatement ifstmt -> {
			final Expression newCond = processExpression(ifstmt.getCondition());
			final Statement[] newThens = processStatements(ifstmt.getThenPart());
			final Statement[] newElses = processStatements(ifstmt.getElsePart());
			yield new IfStatement(ifstmt.getLocation(), newCond, newThens, newElses);
		}
		case final WhileStatement whilestmt -> {
			final Expression newCond = processExpression(whilestmt.getCondition());
			final LoopInvariantSpecification[] newInvs = processLoopSpecifications(whilestmt.getInvariants());
			final Statement[] newBody = processStatements(whilestmt.getBody());
			yield new WhileStatement(whilestmt.getLocation(), newCond, newInvs, newBody);
		}
		case final AtomicStatement atomicstmt -> {
			final Statement[] newBody = processStatements(atomicstmt.getBody());
			yield new AtomicStatement(atomicstmt.getLocation(), newBody);
		}
		case final BreakStatement bs -> new BreakStatement(bs.getLocation(), bs.getLabel());
		case final Label label -> new Label(label.getLocation(), label.getName(), label.getAttributes());
		case final ReturnStatement rs -> new ReturnStatement(rs.getLocation());
		case final GotoStatement gs -> new GotoStatement(gs.getLocation(), gs.getLabels());
		case final ForkStatement forkstmt -> {
			final Expression[] newThreadId = processExpressions(forkstmt.getThreadID());
			final Expression[] newArguments = processExpressions(forkstmt.getArguments());
			yield new ForkStatement(forkstmt.getLoc(), newThreadId, forkstmt.getProcedureName(), newArguments);
		}
		case final JoinStatement joinstmt -> {
			final Expression[] newThreadId = processExpressions(joinstmt.getThreadID());
			final VariableLHS[] newLhs = processVariableLHSs(joinstmt.getLhs());
			yield new JoinStatement(joinstmt.getLoc(), newThreadId, newLhs);
		}
		};
		ModelUtils.copyAnnotations(stat, newStat);
		return newStat;
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		final Expression newExpr = switch (expr) {
		case final BinaryExpression binexp -> {
			final Expression left = processExpression(binexp.getLeft());
			final Expression right = processExpression(binexp.getRight());
			yield new BinaryExpression(expr.getLocation(), binexp.getType(), binexp.getOperator(), left, right);
		}
		case final UnaryExpression unexp -> {
			final Expression subexpr = processExpression(unexp.getExpr());
			yield new UnaryExpression(expr.getLocation(), unexp.getType(), unexp.getOperator(), subexpr);
		}
		case final ArrayAccessExpression aaexpr -> {
			final Expression arr = processExpression(aaexpr.getArray());
			final Expression[] newIndices = processExpressions(aaexpr.getIndices());
			yield new ArrayAccessExpression(aaexpr.getLocation(), aaexpr.getType(), arr, newIndices);
		}
		case final ArrayStoreExpression aaexpr -> {
			final Expression arr = processExpression(aaexpr.getArray());
			final Expression value = processExpression(aaexpr.getValue());
			final Expression[] newIndices = processExpressions(aaexpr.getIndices());
			yield new ArrayStoreExpression(aaexpr.getLocation(), aaexpr.getType(), arr, newIndices, value);
		}
		case final BitVectorAccessExpression bvaexpr -> {
			final Expression bv = processExpression(bvaexpr.getBitvec());
			yield new BitVectorAccessExpression(bvaexpr.getLocation(), bvaexpr.getType(), bv, bvaexpr.getEnd(),
					bvaexpr.getStart());
		}
		case final FunctionApplication app -> {
			final Expression[] args = processExpressions(app.getArguments());
			yield new FunctionApplication(app.getLocation(), app.getType(), app.getIdentifier(), args);
		}
		case final IfThenElseExpression ite -> {
			final Expression cond = processExpression(ite.getCondition());
			final Expression thenPart = processExpression(ite.getThenPart());
			final Expression elsePart = processExpression(ite.getElsePart());
			yield new IfThenElseExpression(ite.getLocation(), thenPart.getType(), cond, thenPart, elsePart);
		}
		case final QuantifierExpression quant -> {
			final Attribute[] newAttrs = processAttributes(quant.getAttributes());
			final VarList[] newParams = processVarLists(quant.getParameters());
			final Expression subform = processExpression(quant.getSubformula());
			yield new QuantifierExpression(quant.getLocation(), quant.getType(), quant.isUniversal(),
					quant.getTypeParams(), newParams, newAttrs, subform);
		}
		case final StructConstructor sConst -> {
			final Expression[] fieldValues = processExpressions(sConst.getFieldValues());
			yield new StructConstructor(sConst.getLocation(), sConst.getFieldIdentifiers(), fieldValues);
		}
		case final StructAccessExpression sae -> {
			final Expression struct = processExpression(sae.getStruct());
			yield new StructAccessExpression(sae.getLocation(), struct, sae.getField());
		}

		case final BooleanLiteral bl -> new BooleanLiteral(bl.getLocation(), bl.getType(), bl.getValue());
		case final IntegerLiteral il -> new IntegerLiteral(il.getLocation(), il.getType(), il.getValue());
		case final BitvecLiteral bvl ->
				new BitvecLiteral(bvl.getLocation(), bvl.getType(), bvl.getValue(), bvl.getLength());
		case final StringLiteral sl -> new StringLiteral(sl.getLocation(), sl.getType(), sl.getValue());
		case final IdentifierExpression ie -> new IdentifierExpression(ie.getLocation(), ie.getType(),
				ie.getIdentifier(), ie.getDeclarationInformation());
		case final WildcardExpression we -> new WildcardExpression(we.getLocation(), we.getType());
		case final RealLiteral rl -> new RealLiteral(rl.getLocation(), rl.getType(), rl.getValue());
		};
		ModelUtils.copyAnnotations(expr, newExpr);
		return newExpr;
	}
}
