/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.visitors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.annotations.UseDefSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class UseDefVisitor extends SimpleRCFGVisitor {

	public UseDefVisitor(ILogger logger) {
		super(logger);
	}

	@Override
	public void pre(IcfgEdge edge) {
		super.pre(edge);
		final UseDefSequence annot = new UseDefSequence();
		if (edge instanceof StatementSequence) {
			for (final Statement s : ((StatementSequence) edge).getStatements()) {
				annot.Sequence.add(processStatement(s));
			}
		} else if (edge instanceof Call) {
			annot.Sequence.add(processStatement(((Call) edge)
					.getCallStatement()));
		} else if (edge instanceof GotoEdge) {
			mLogger.info("Ignoring GotoEdge edge " + edge);
			return;
		} else if (edge instanceof ParallelComposition) {
			mLogger.info("Ignoring ParallelComposition edge " + edge);
			return;
		} else if (edge instanceof Return) {
			mLogger.info("Ignoring Return edge " + edge);
			return;
		} else if (edge instanceof SequentialComposition) {
			mLogger.info("Ignoring SequentialComposition edge " + edge);
			return;
		} else if (edge instanceof StatementSequence) {
			mLogger.info("Ignoring StatementSequence edge " + edge);
			return;
		} else if (edge instanceof Summary) {
			mLogger.info("Ignoring summary edge " + edge);
			return;

		} else if (edge instanceof RootEdge) {
			mLogger.info("Ignoring root edge " + edge);
			return;
		} else {
			mLogger.debug("Unknown edge type: "
					+ edge.getClass().getCanonicalName() + " " + edge);
			return;
		}

		annot.addAnnotation(edge);

	}

	private UseDefSet processStatement(Statement stmt) {
		UseDefSet uds = new UseDefSet();
		if (stmt instanceof AssignmentStatement) {
			final AssignmentStatement assign = (AssignmentStatement) stmt;
			for (final LeftHandSide lhs : assign.getLhs()) {
				uds = uds.merge(processLeftHandSide(lhs));
			}
			for (final Expression rhs : assign.getRhs()) {
				uds = uds.merge(processExpression(rhs));
			}
			return uds;

		} else if (stmt instanceof AssertStatement) {

		} else if (stmt instanceof AssumeStatement) {
			return processExpression(((AssumeStatement) stmt).getFormula());

		} else if (stmt instanceof BreakStatement) {
			return uds;

		} else if (stmt instanceof CallStatement) {
			final CallStatement call = (CallStatement) stmt;
			for (final VariableLHS id : call.getLhs()) {
				uds.Def.add(id.toString());
			}
			for (final Expression exp : call.getArguments()) {
				uds = uds.merge(processExpression(exp));
			}
			return uds;

		} else if (stmt instanceof GotoStatement) {
			return uds;

		} else if (stmt instanceof HavocStatement) {
			for (final VariableLHS id : ((HavocStatement) stmt).getIdentifiers()) {
				uds.Def.add(id.toString());
			}
			return uds;

		} else if (stmt instanceof IfStatement) {

			final IfStatement ifstmt = (IfStatement) stmt;
			mLogger.debug("IfStatement in edge?");

			uds = processExpression(ifstmt.getCondition());
			for (final Statement s : ifstmt.getThenPart()) {
				uds = uds.merge(processStatement(s));
			}
			for (final Statement s : ifstmt.getElsePart()) {
				uds = uds.merge(processStatement(s));
			}

			return uds;

		} else if (stmt instanceof Label) {
			return uds;
		} else if (stmt instanceof ReturnStatement) {
			return uds;
		} else if (stmt instanceof WhileStatement) {
			final WhileStatement wstmt = (WhileStatement) stmt;
			mLogger.debug("WhileStatement in edge?");
			uds = processExpression(wstmt.getCondition());
			for (final Statement s : wstmt.getBody()) {
				uds = uds.merge(processStatement(s));
			}

			return uds;
		}
		mLogger.debug("Unknown statement type: "
				+ stmt.getClass().getCanonicalName() + " " + stmt);
		return uds;
	}

	private UseDefSet processExpression(Expression exp) {
		UseDefSet uds = new UseDefSet();
		if (exp instanceof ArrayAccessExpression) {
			final ArrayAccessExpression aaexp = (ArrayAccessExpression) exp;
			uds = uds.merge(processExpression(aaexp.getArray()));
			for (final Expression e : aaexp.getIndices()) {
				uds = uds.merge(processExpression(e));
			}
			return uds;
		} else if (exp instanceof ArrayStoreExpression) {

		} else if (exp instanceof BinaryExpression) {
			final BinaryExpression bexp = (BinaryExpression) exp;
			return processExpression(bexp.getLeft()).merge(
					processExpression(bexp.getRight()));

		} else if (exp instanceof BitvecLiteral) {
			return uds;

		} else if (exp instanceof BitVectorAccessExpression) {

		} else if (exp instanceof BooleanLiteral) {
			return uds;

		} else if (exp instanceof FunctionApplication) {
			for (final Expression argument : ((FunctionApplication) exp)
					.getArguments()) {
				uds = uds.merge(processExpression(argument));
			}
			return uds;

		} else if (exp instanceof IdentifierExpression) {
			uds.Use.add(((IdentifierExpression) exp).getIdentifier());
			return uds;

		} else if (exp instanceof IfThenElseExpression) {
			final IfThenElseExpression ifexp = (IfThenElseExpression) exp;
			uds = uds.merge(processExpression(ifexp.getCondition()));
			uds = uds.merge(processExpression(ifexp.getThenPart()));
			uds = uds.merge(processExpression(ifexp.getElsePart()));
			return uds;

		} else if (exp instanceof IntegerLiteral) {
			return uds;

		} else if (exp instanceof QuantifierExpression) {
			mLogger.warn("Ignoring quantifier expression");
			return uds;

		} else if (exp instanceof RealLiteral) {
			return uds;

		} else if (exp instanceof StringLiteral) {
			return uds;

		} else if (exp instanceof StructAccessExpression) {

		} else if (exp instanceof UnaryExpression) {
			return processExpression(((UnaryExpression) exp).getExpr());

		} else if (exp instanceof WildcardExpression) {
			return uds;
		}

		mLogger.debug("Unknown expression type: "
				+ exp.getClass().getCanonicalName() + " " + exp);
		return uds;
	}

	private UseDefSet processLeftHandSide(LeftHandSide lhs) {
		final UseDefSet uds = new UseDefSet();
		if (lhs instanceof ArrayLHS) {

		} else if (lhs instanceof StructLHS) {

		} else if (lhs instanceof VariableLHS) {
			uds.Def.add(((VariableLHS) lhs).getIdentifier());
			return uds;
		}

		mLogger.debug("Unknown LeftHandSide type: "
				+ lhs.getClass().getCanonicalName() + " " + lhs);
		return uds;
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean abortCurrentBranch() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean abortAll() {
		// TODO Auto-generated method stub
		return false;
	}

}
