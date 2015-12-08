package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.util;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

public interface IStatementVisitor {
	boolean visitStatement(Statement stmt);

	void visitedStatement(Statement stmt);

	void visit(AssertStatement assertStatement);

	void visit(BreakStatement breakStatement);

	void visit(CallStatement callStatement);

	void visit(AssignmentStatement assignmentStatement);

	void visit(AssumeStatement assumeStatement);

	void visit(GotoStatement gotoStatement);

	void visit(HavocStatement havocStatement);

	void visit(IfStatement ifStatement);

	void visit(Label label);

	void visit(WhileStatement whileStatement);

	void visitReturn(CallStatement callStatement);
}