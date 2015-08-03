package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

public interface IStatementVisitor
{
	void visitStatement(Statement stmt);
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
	void visit(ReturnStatement returnStatement);
	void visit(WhileStatement whileStatement);
}