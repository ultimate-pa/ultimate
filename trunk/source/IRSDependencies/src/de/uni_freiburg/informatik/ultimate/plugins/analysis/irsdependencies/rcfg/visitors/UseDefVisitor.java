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
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.icfg.Call;
import de.uni_freiburg.informatik.ultimate.lib.icfg.GotoEdge;
import de.uni_freiburg.informatik.ultimate.lib.icfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.lib.icfg.Return;
import de.uni_freiburg.informatik.ultimate.lib.icfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.lib.icfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.lib.icfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.lib.icfg.Summary;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.annotations.UseDefSequence;

public class UseDefVisitor extends SimpleRCFGVisitor {

	public UseDefVisitor(final ILogger logger) {
		super(logger);
	}

	@Override
	public void pre(final IcfgEdge edge) {
		super.pre(edge);
		final UseDefSequence annot = new UseDefSequence();
		if (edge instanceof StatementSequence) {
			for (final Statement s : ((StatementSequence) edge).getStatements()) {
				annot.Sequence.add(processStatement(s));
			}
		} else if (edge instanceof Call) {
			annot.Sequence.add(processStatement(((Call) edge).getCallStatement()));
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
		} else if (edge instanceof Summary) {
			mLogger.info("Ignoring summary edge " + edge);
			return;
		} else if (edge instanceof RootEdge) {
			mLogger.info("Ignoring root edge " + edge);
			return;
		} else {
			mLogger.debug("Unknown edge type: " + edge.getClass().getCanonicalName() + " " + edge);
			return;
		}

		annot.addAnnotation(edge);
	}

	private UseDefSet processStatement(final Statement stmt) {
		UseDefSet uds = new UseDefSet();

		switch (stmt) {
		case final AssignmentStatement assign:
			for (final LeftHandSide lhs : assign.getLhs()) {
				uds = uds.merge(processLeftHandSide(lhs));
			}
			for (final Expression rhs : assign.getRhs()) {
				uds = uds.merge(processExpression(rhs));
			}
			return uds;

		case final AssumeStatement assume:
			return processExpression(assume.getFormula());

		case final CallStatement call:
			for (final VariableLHS id : call.getLhs()) {
				uds.Def.add(id.toString());
			}
			for (final Expression exp : call.getArguments()) {
				uds = uds.merge(processExpression(exp));
			}
			return uds;

		case final HavocStatement havocStmt:
			for (final VariableLHS id : havocStmt.getIdentifiers()) {
				uds.Def.add(id.toString());
			}
			return uds;

		case final IfStatement ifStmt:
			mLogger.debug("IfStatement in edge?");
			uds = processExpression(ifStmt.getCondition());
			for (final Statement s : ifStmt.getThenPart()) {
				uds = uds.merge(processStatement(s));
			}
			for (final Statement s : ifStmt.getElsePart()) {
				uds = uds.merge(processStatement(s));
			}
			return uds;

		case final WhileStatement whileStmt:
			mLogger.debug("WhileStatement in edge?");
			uds = processExpression(whileStmt.getCondition());
			for (final Statement s : whileStmt.getBody()) {
				uds = uds.merge(processStatement(s));
			}
			return uds;

		case final BreakStatement breakStmt:
			return uds;
		case final GotoStatement gotoStmt:
			return uds;
		case final Label label:
			return uds;
		case final ReturnStatement returnStmt:
			return uds;

		case final ForkStatement forkStmt:
			mLogger.debug("Unsupported statement type: " + stmt.getClass().getCanonicalName() + " " + stmt);
			return uds;
		case final JoinStatement joinStmt:
			mLogger.debug("Unsupported statement type: " + stmt.getClass().getCanonicalName() + " " + stmt);
			return uds;
		case final AssertStatement assertStmt:
			mLogger.debug("Unsupported statement type: " + stmt.getClass().getCanonicalName() + " " + stmt);
			return uds;
		case final AtomicStatement atomicStmt:
			mLogger.debug("Unsupported statement type: " + stmt.getClass().getCanonicalName() + " " + stmt);
			return uds;
		}
	}

	private UseDefSet processExpression(final Expression exp) {
		UseDefSet uds = new UseDefSet();

		switch (exp) {
		case final ArrayAccessExpression aaexp:
			uds = uds.merge(processExpression(aaexp.getArray()));
			for (final Expression e : aaexp.getIndices()) {
				uds = uds.merge(processExpression(e));
			}
			return uds;

		case final BinaryExpression bexp:
			return processExpression(bexp.getLeft()).merge(processExpression(bexp.getRight()));

		case final FunctionApplication app:
			for (final Expression argument : app.getArguments()) {
				uds = uds.merge(processExpression(argument));
			}
			return uds;

		case final IdentifierExpression id:
			uds.Use.add(id.getIdentifier());
			return uds;

		case final IfThenElseExpression ite:
			uds = uds.merge(processExpression(ite.getCondition()));
			uds = uds.merge(processExpression(ite.getThenPart()));
			uds = uds.merge(processExpression(ite.getElsePart()));
			return uds;

		case final UnaryExpression uexp:
			return processExpression(uexp.getExpr());

		case final BitvecLiteral bvLit:
			return uds;
		case final BooleanLiteral boolLit:
			return uds;
		case final IntegerLiteral intLit:
			return uds;
		case final RealLiteral realLit:
			return uds;
		case final StringLiteral stringLit:
			return uds;
		case final WildcardExpression wild:
			return uds;

		case final QuantifierExpression quant:
			mLogger.warn("Ignoring quantifier expression");
			return uds;

		case final StructAccessExpression sae:
			mLogger.debug("Unsupported expression type: " + exp.getClass().getCanonicalName() + " " + exp);
			return uds;
		case final ArrayStoreExpression ase:
			mLogger.debug("Unsupported expression type: " + exp.getClass().getCanonicalName() + " " + exp);
			return uds;
		case final StructConstructor scon:
			mLogger.debug("Unsupported expression type: " + exp.getClass().getCanonicalName() + " " + exp);
			return uds;
		case final BitVectorAccessExpression bvae:
			mLogger.debug("Unsupported expression type: " + exp.getClass().getCanonicalName() + " " + exp);
			return uds;
		}
	}

	private UseDefSet processLeftHandSide(final LeftHandSide lhs) {
		final UseDefSet uds = new UseDefSet();

		if (lhs instanceof final VariableLHS variable) {
			uds.Def.add(variable.getIdentifier());
			return uds;
		}

		mLogger.debug("Unknown LeftHandSide type: " + lhs.getClass().getCanonicalName() + " " + lhs);
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
