package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.util;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.*;

public class RCFGWalker {
	private final IRCFGVisitor mVisitor;

	public RCFGWalker(IRCFGVisitor visitor) {
		mVisitor = visitor;
	}

	public void visit(RCFGEdge e) {
		mVisitor.visitEdge(e);
		if (e instanceof CodeBlock) {
			visit((CodeBlock) e);
		} else if (e instanceof RootEdge) {
			visit((RootEdge) e);
		} else {
			throw new UnsupportedOperationException("Extend the new type");
		}
		mVisitor.visitedEdge(e);
	}

	protected void visit(RootEdge e) {
		mVisitor.visit(e);
	}

	protected void visit(CodeBlock c) {
		mVisitor.visitCodeBlock(c);
		if (c instanceof StatementSequence) {
			visit((StatementSequence) c);
		} else if (c instanceof Call) {
			visit((Call) c);
		} else if (c instanceof GotoEdge) {
			visit((GotoEdge) c);
		} else if (c instanceof ParallelComposition) {
			visit((ParallelComposition) c);
		} else if (c instanceof Return) {
			visit((Return) c);
		} else if (c instanceof SequentialComposition) {
			visit((SequentialComposition) c);
		} else if (c instanceof Summary) {
			visit((Summary) c);
		} else {
			throw new UnsupportedOperationException("Extend the new type");
		}
		mVisitor.visitedCodeBlock(c);
	}

	protected void visit(Call c) {
		mVisitor.visit(c);
		visit(c.getCallStatement(), null);
		mVisitor.visited(c);
	}

	protected void visit(GotoEdge c) {
		mVisitor.visit(c);
	}

	protected void visit(ParallelComposition c) {
		mVisitor.visit(c);
		for (CodeBlock b : c.getCodeBlocks()) {
			visit(b);
		}
		mVisitor.visited(c);
	}

	protected void visit(Return c) {
		mVisitor.visit(c);
		mVisitor.getStatementVisitor().visitReturn(c.getCallStatement());
		mVisitor.visited(c);
	}

	protected void visit(SequentialComposition c) {
		mVisitor.visit(c);
		for (CodeBlock b : c.getCodeBlocks()) {
			visit(b);
		}
		mVisitor.visited(c);
	}

	protected void visit(Summary c) {
		mVisitor.visit(c);
	}

	protected void visit(StatementSequence c) {
		mVisitor.visit(c);
		for (Statement s : c.getStatements()) {
			visit(s, null);
		}
		mVisitor.visited(c);
	}

	public void visit(Statement stmt, CallStatement cStmt) {
		IStatementVisitor sv = mVisitor.getStatementVisitor();
		if (sv.visitStatement(stmt)) {
			if (stmt instanceof AssertStatement) {
				sv.visit((AssertStatement) stmt);
			} else if (stmt instanceof AssignmentStatement) {
				sv.visit((AssignmentStatement) stmt);
			} else if (stmt instanceof AssumeStatement) {
				sv.visit((AssumeStatement) stmt);
			} else if (stmt instanceof BreakStatement) {
				sv.visit((BreakStatement) stmt);
			} else if (stmt instanceof CallStatement) {
				sv.visit((CallStatement) stmt);
			} else if (stmt instanceof GotoStatement) {
				sv.visit((GotoStatement) stmt);
			} else if (stmt instanceof HavocStatement) {
				sv.visit((HavocStatement) stmt);
			} else if (stmt instanceof IfStatement) {
				sv.visit((IfStatement) stmt);
			} else if (stmt instanceof Label) {
				sv.visit((Label) stmt);
				// } else if(stmt instanceof ReturnStatement) {
				// sv.visit((ReturnStatement)stmt, cStmt);
			} else if (stmt instanceof WhileStatement) {
				sv.visit((WhileStatement) stmt);
			} else {
				throw new UnsupportedOperationException("Extend the new type");
			}
			sv.visitedStatement(stmt);
		}
	}
}
