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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 * A (real) implementation of the visitor pattern.
 * Visits all edges of an RCFG (CodeBlocks) and the 
 * nodes (Statements) in the 
 * 
 * Every RCFGEdge must implement an accept method 
 * in which it calls visit, accept of its children
 * and call visited.
 * 
 * It also calls a visit method for supertypes
 * 
 * @author GROSS-JAN
 *
 */
public interface IRCFGVisitor
{
	/* --- edges / CodeBocks --- */
	void visitEdge(RCFGEdge e);
	void visitedEdge(RCFGEdge e);
	
	void visitCodeBlock(CodeBlock e);
	void visitedCodeBlock(CodeBlock e);
	
	void visit(Call c);	
	void visit(Return c);
	void visit(GotoEdge c);	
	void visit(RootEdge c);
	
	void visit(ParallelComposition c);
	void visit(Summary c);
	void visit(SequentialComposition c);	
	void visit(StatementSequence c);
			
	void visited(ParallelComposition c);	
	void visited(Summary c);		
	void visited(SequentialComposition c);
	void visited(StatementSequence c);

	
	/* --- nodes / Statements --- */

//	void visitStatement(Statement e);
//	void visitedStatement(Statement e);
//		
//	void visit(AssertStatement s);
//	void visit(AssignmentStatement s);
//	void visit(AssumeStatement s);
//	void visit(BreakStatement s);
//	void visit(CallStatement s);
//	void visit(GotoStatement s);
//	void visit(HavocStatement s);
//	void visit(IfStatement s);
//	void visit(Label s);
//	void visit(ReturnStatement s);
//	void visit(WhileStatement s);
	
	/**
	 * The visitor used to go through statements
	 * of the statement sequences
	 * @return
	 */
	IStatementVisitor getStatementVisitor();
	
	StatementWalker getStatementWalker();
}
