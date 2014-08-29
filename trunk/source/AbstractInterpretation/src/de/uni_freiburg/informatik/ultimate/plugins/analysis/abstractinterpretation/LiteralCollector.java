/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

/**
 * Collects int and real literals found in an RCFG.
 * Some widening operators use these.
 * 
 * @author Christopher Dillo
 */
public class LiteralCollector extends RCFGEdgeVisitor {
	
	private final Set<String> m_literals = new HashSet<String>();
	
	private final Logger m_logger;
	
	private final Set<RCFGEdge> m_visitedEdges = new HashSet<RCFGEdge>();
	
	public LiteralCollector(RootNode root, Logger logger) {
		m_logger = logger;
		
		for (RCFGEdge e : root.getOutgoingEdges())
			visit(e);
	}
	
	public Set<String> getResult() {
		return m_literals;
	}

	@Override
	protected void visit(RCFGEdge e) {
		if (m_visitedEdges.contains(e))
			return;
		
		m_visitedEdges.add(e);

		super.visit(e);
		
		// visit outgoing edges of target node
		for (RCFGEdge edge : e.getTarget().getOutgoingEdges())
			visit(edge);
	}

	@Override
	protected void visit(CodeBlock c) {
		super.visit(c);
	}

	@Override
	protected void visit(ParallelComposition c) {
		super.visit(c);

		Collection<CodeBlock> blocks = c.getBranchIndicator2CodeBlock().values();

		for (CodeBlock b : blocks)
			visit(b);
	}

	@Override
	protected void visit(SequentialComposition c) {
		super.visit(c);

		CodeBlock[] blocks = c.getCodeBlocks();

		for (CodeBlock b : blocks)
			visit(b);
	}

	@Override
	protected void visit(Summary c) {
		super.visit(c);
	}

	@Override
	protected void visit(StatementSequence c) {
		super.visit(c);

		List<Statement> statements = c.getStatements();

		for (Statement s : statements)
			visit(s);
	}

	public void visit(Statement statement) {
		if (statement instanceof ReturnStatement) {
			visit((ReturnStatement) statement);
		} else if (statement instanceof HavocStatement) {
			visit((HavocStatement) statement);
		} else if (statement instanceof CallStatement) {
			visit((CallStatement) statement);
		} else if (statement instanceof AssignmentStatement) {
			visit((AssignmentStatement) statement);
		} else if (statement instanceof AssumeStatement) {
			visit((AssumeStatement) statement);
		} else {
			m_logger.error(String.format("Unsupported statement type %s", statement.getClass()));
		}
	}

	protected void visit(ReturnStatement statement) {
		// no literals to collect
	}

	protected void visit(HavocStatement statement) {
		// no literals to collect
	}

	protected void visit(CallStatement statement) {
		Expression[] args = statement.getArguments();
		for (Expression e : args)
			visit(e);
	}

	protected void visit(AssignmentStatement statement) {
		Expression[] rhs = statement.getRhs();

		for (Expression e : rhs)
			visit(e);
	}

	protected void visit(AssumeStatement statement) {
		visit(statement.getFormula());
	}

	protected void visit(Expression expr) {
		if (expr instanceof ArrayAccessExpression) {
			visit((ArrayAccessExpression) expr);
		} else if (expr instanceof ArrayStoreExpression) {
			visit((ArrayStoreExpression) expr);
		} else if (expr instanceof BinaryExpression) {
			visit((BinaryExpression) expr);
		} else if (expr instanceof BitvecLiteral) {
			visit((BitvecLiteral) expr);
		} else if (expr instanceof BitVectorAccessExpression) {
			visit((BitVectorAccessExpression) expr);
		} else if (expr instanceof BooleanLiteral) {
			visit((BooleanLiteral) expr);
		} else if (expr instanceof IdentifierExpression) {
			visit((IdentifierExpression) expr);
		} else if (expr instanceof IntegerLiteral) {
			visit((IntegerLiteral) expr);
		} else if (expr instanceof RealLiteral) {
			visit((RealLiteral) expr);
		} else if (expr instanceof StringLiteral) {
			visit((StringLiteral) expr);
		} else if (expr instanceof StructAccessExpression) {
			visit((StructAccessExpression) expr);
		} else if (expr instanceof StructConstructor) {
			visit((StructConstructor) expr);
		} else if (expr instanceof UnaryExpression) {
			visit((UnaryExpression) expr);
		} else if (expr instanceof FunctionApplication) {
			visit((FunctionApplication) expr);
		} else if (expr instanceof IfThenElseExpression) {
			visit((IfThenElseExpression) expr);
		} else {
			m_logger.error(String.format("Extend this with new type %s", expr.getClass()));
		}
	}

	protected void visit(UnaryExpression expr) {
		visit(expr.getExpr());
	}

	protected void visit(StructConstructor expr) {
		// no literals to collect
	}

	protected void visit(StructAccessExpression expr) {
		visit(expr.getStruct());
	}

	protected void visit(StringLiteral expr) {
		// no number literals to collect
	}

	protected void visit(RealLiteral expr) {
		if (m_literals.add(expr.getValue()))
			m_logger.debug(String.format("Collected real literal \"%s\"", expr.getValue()));
	}

	protected void visit(IntegerLiteral expr) {
		if (m_literals.add(expr.getValue()))
			m_logger.debug(String.format("Collected int literal \"%s\"", expr.getValue()));
	}

	protected void visit(IdentifierExpression expr) {
		// no literals to collect
	}

	protected void visit(BooleanLiteral expr) {
		// no number literals to collect
	}

	protected void visit(BitVectorAccessExpression expr) {
		// no literals to collect
	}

	protected void visit(BitvecLiteral expr) {
		// no number literals to collect
	}

	protected void visit(BinaryExpression expr) {
		visit(expr.getLeft());
		visit(expr.getRight());
	}

	protected void visit(ArrayStoreExpression expr) {
		visit(expr.getValue());
		for (Expression e : expr.getIndices())
			visit(e);
	}

	protected void visit(ArrayAccessExpression expr) {
		for (Expression e : expr.getIndices())
			visit(e);
	}
	
	private void visit(IfThenElseExpression expr) {
		visit(expr.getCondition());
		visit(expr.getThenPart());
		visit(expr.getElsePart());
	}

	protected void visit(FunctionApplication expr) {
		for (Expression e : expr.getArguments())
			visit(e);
	}
	
	
}
