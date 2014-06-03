package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors;

import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.annotations.UseDefSequence;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class UseDefVisitor extends SimpleRCFGVisitor {



	@Override
	public void pre(RCFGEdge edge) {
		super.pre(edge);
		UseDefSequence annot = new UseDefSequence();
		if (edge instanceof StatementSequence) {
			for (Statement s : ((StatementSequence) edge).getStatements()) {
				annot.Sequence.add(processStatement(s));
			}
		} else if (edge instanceof Call) {
			annot.Sequence.add(processStatement(((Call) edge)
					.getCallStatement()));
		} else if (edge instanceof GotoEdge) {
			sLogger.info("Ignoring GotoEdge edge " + edge);
			return;
		} else if (edge instanceof ParallelComposition) {
			sLogger.info("Ignoring ParallelComposition edge " + edge);
			return;
		} else if (edge instanceof Return) {
			sLogger.info("Ignoring Return edge " + edge);
			return;
		} else if (edge instanceof SequentialComposition) {
			sLogger.info("Ignoring SequentialComposition edge " + edge);
			return;
		} else if (edge instanceof StatementSequence) {
			sLogger.info("Ignoring StatementSequence edge " + edge);
			return;
		} else if (edge instanceof Summary) {
			sLogger.info("Ignoring summary edge " + edge);
			return;

		} else if (edge instanceof RootEdge) {
			sLogger.info("Ignoring root edge " + edge);
			return;
		} else {
			sLogger.debug("Unknown edge type: "
					+ edge.getClass().getCanonicalName() + " " + edge);
			return;
		}

		annot.addAnnotation(edge);

	}

	private UseDefSet processStatement(Statement stmt) {
		UseDefSet uds = new UseDefSet();
		if (stmt instanceof AssignmentStatement) {
			AssignmentStatement assign = (AssignmentStatement) stmt;
			for (LeftHandSide lhs : assign.getLhs()) {
				uds = uds.merge(processLeftHandSide(lhs));
			}
			for (Expression rhs : assign.getRhs()) {
				uds = uds.merge(processExpression(rhs));
			}
			return uds;

		} else if (stmt instanceof AssertStatement) {

		} else if (stmt instanceof AssumeStatement) {
			return processExpression(((AssumeStatement) stmt).getFormula());

		} else if (stmt instanceof BreakStatement) {
			return uds;

		} else if (stmt instanceof CallStatement) {
			CallStatement call = (CallStatement) stmt;
			for (VariableLHS id : call.getLhs()) {
				uds.Def.add(id.toString());
			}
			for (Expression exp : call.getArguments()) {
				uds = uds.merge(processExpression(exp));
			}
			return uds;

		} else if (stmt instanceof GotoStatement) {
			return uds;

		} else if (stmt instanceof HavocStatement) {
			for (VariableLHS id : ((HavocStatement) stmt).getIdentifiers()) {
				uds.Def.add(id.toString());
			}
			return uds;

		} else if (stmt instanceof IfStatement) {

			IfStatement ifstmt = (IfStatement) stmt;
			sLogger.debug("IfStatement in edge?");

			uds = processExpression(ifstmt.getCondition());
			for (Statement s : ifstmt.getThenPart()) {
				uds = uds.merge(processStatement(s));
			}
			for (Statement s : ifstmt.getElsePart()) {
				uds = uds.merge(processStatement(s));
			}

			return uds;

		} else if (stmt instanceof Label) {
			return uds;
		} else if (stmt instanceof ReturnStatement) {
			return uds;
		} else if (stmt instanceof WhileStatement) {
			WhileStatement wstmt = (WhileStatement) stmt;
			sLogger.debug("WhileStatement in edge?");
			uds = processExpression(wstmt.getCondition());
			for (Statement s : wstmt.getBody()) {
				uds = uds.merge(processStatement(s));
			}

			return uds;
		}
		sLogger.debug("Unknown statement type: "
				+ stmt.getClass().getCanonicalName() + " " + stmt);
		return uds;
	}

	private UseDefSet processExpression(Expression exp) {
		UseDefSet uds = new UseDefSet();
		if (exp instanceof ArrayAccessExpression) {
			ArrayAccessExpression aaexp = (ArrayAccessExpression) exp;
			uds = uds.merge(processExpression(aaexp.getArray()));
			for (Expression e : aaexp.getIndices()) {
				uds = uds.merge(processExpression(e));
			}
			return uds;
		} else if (exp instanceof ArrayStoreExpression) {

		} else if (exp instanceof BinaryExpression) {
			BinaryExpression bexp = (BinaryExpression) exp;
			return processExpression(bexp.getLeft()).merge(
					processExpression(bexp.getRight()));

		} else if (exp instanceof BitvecLiteral) {
			return uds;

		} else if (exp instanceof BitVectorAccessExpression) {

		} else if (exp instanceof BooleanLiteral) {
			return uds;

		} else if (exp instanceof FunctionApplication) {
			for (Expression argument : ((FunctionApplication) exp)
					.getArguments()) {
				uds = uds.merge(processExpression(argument));
			}
			return uds;

		} else if (exp instanceof IdentifierExpression) {
			uds.Use.add(((IdentifierExpression) exp).getIdentifier());
			return uds;

		} else if (exp instanceof IfThenElseExpression) {
			IfThenElseExpression ifexp = (IfThenElseExpression) exp;
			uds = uds.merge(processExpression(ifexp.getCondition()));
			uds = uds.merge(processExpression(ifexp.getThenPart()));
			uds = uds.merge(processExpression(ifexp.getElsePart()));
			return uds;

		} else if (exp instanceof IntegerLiteral) {
			return uds;

		} else if (exp instanceof QuantifierExpression) {
			sLogger.warn("Ignoring quantifier expression");
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

		sLogger.debug("Unknown expression type: "
				+ exp.getClass().getCanonicalName() + " " + exp);
		return uds;
	}

	private UseDefSet processLeftHandSide(LeftHandSide lhs) {
		UseDefSet uds = new UseDefSet();
		if (lhs instanceof ArrayLHS) {

		} else if (lhs instanceof StructLHS) {

		} else if (lhs instanceof VariableLHS) {
			uds.Def.add(((VariableLHS) lhs).getIdentifier());
			return uds;
		}

		sLogger.debug("Unknown LeftHandSide type: "
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
