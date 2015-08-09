package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

/**
 * Extracts a List of {@link Statement}s from a {@link RCFGEdge}.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class RcfgStatementExtractor extends RCFGEdgeVisitor {

	private List<Statement> mStatements;

	public List<Statement> process(RCFGEdge edge) {
		mStatements = new ArrayList<Statement>();
		visit(edge);
		return mStatements;
	}

	@Override
	protected void visit(StatementSequence c) {
		mStatements.addAll(c.getStatements());
		super.visit(c);
	}

}
