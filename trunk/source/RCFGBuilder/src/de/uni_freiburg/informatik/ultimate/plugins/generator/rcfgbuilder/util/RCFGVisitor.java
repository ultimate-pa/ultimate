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
 * An empty implementation of the IRCFGVisitor visitor pattern
 * 
 * @author GROSS-JAN
 *
 */
public class RCFGVisitor implements IRCFGVisitor
{
	private static StatementWalker sStatementWalker = new StatementWalker();

	private final IStatementVisitor mStatementVisitor;
	
	/**
	 * Constructor
	 * 
	 * @param statementVisitor
	 */
	public RCFGVisitor(IStatementVisitor statementVisitor)
	{
		mStatementVisitor = statementVisitor;
	}
	
	@Override
	public void visitEdge(RCFGEdge e)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitedEdge(RCFGEdge e)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitCodeBlock(CodeBlock e)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitedCodeBlock(CodeBlock e)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visit(Call c)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visit(Return c)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visit(GotoEdge c)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visit(RootEdge c)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visit(ParallelComposition c)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visit(Summary c)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visit(SequentialComposition c)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visit(StatementSequence c)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visited(ParallelComposition c)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visited(Summary c)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visited(SequentialComposition c)	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visited(StatementSequence c)	{
		// TODO Auto-generated method stub
		
	}

	

	@Override
	public IStatementVisitor getStatementVisitor()	{
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public StatementWalker getStatementWalker()	{
		return sStatementWalker;
	}	
}
