package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;

/**
 * Since the ast is generated we need this walker
 * instead of letting the statement accept the IStatementVisitor
 * @author GROSS-JAN
 *
 */
public class StatementWalker
{
	public void walk(Statement stmt, IStatementVisitor statementVisitor)
	{
		statementVisitor.visitStatement(stmt);
		
		if(stmt instanceof AssertStatement) {
			statementVisitor.visit((AssertStatement)stmt);		
		} else if(stmt instanceof AssignmentStatement) {
			statementVisitor.visit((AssignmentStatement)stmt);
		} else if(stmt instanceof AssumeStatement) {
			statementVisitor.visit((AssumeStatement)stmt);
		} else if(stmt instanceof BreakStatement) {
			statementVisitor.visit((BreakStatement)stmt);
		} else if(stmt instanceof CallStatement) {
			statementVisitor.visit((CallStatement)stmt);
		} else if(stmt instanceof GotoStatement) {
			statementVisitor.visit((GotoStatement)stmt);
		} else if(stmt instanceof HavocStatement) {
			statementVisitor.visit((HavocStatement)stmt);
		} else if(stmt instanceof IfStatement) {
			statementVisitor.visit((IfStatement)stmt);
		} else if(stmt instanceof Label) {
			statementVisitor.visit((Label)stmt);
		} else if(stmt instanceof ReturnStatement) {
			statementVisitor.visit((ReturnStatement)stmt);
		} else if(stmt instanceof WhileStatement) {
			statementVisitor.visit((WhileStatement)stmt);
		} else {			
			throw new UnsupportedOperationException("Extend the new type");
		}
		statementVisitor.visitedStatement(stmt);
	}
}
