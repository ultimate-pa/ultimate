package de.uni_freiburg.informatik.ultimate.reachingdefinitions.trace;

import java.util.ArrayList;
import java.util.List;


import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.annotations.ReachDefStatementAnnotation;

public class ReachDefTracePredecessorGenerator extends RCFGEdgeVisitor {

	private final String mAnnotationSuffix;

	public ReachDefTracePredecessorGenerator(String annotationSuffix) {
		mAnnotationSuffix = annotationSuffix;
	}

	private List<ReachDefStatementAnnotation> rtr;

	/**
	 * Returns all {@link ReachDefStatementAnnotation}s from the predecessor
	 * 
	 * @param e
	 * @return
	 */
	public List<ReachDefStatementAnnotation> process(CodeBlock predecessor) {
		rtr = new ArrayList<ReachDefStatementAnnotation>();
		visit(predecessor);
		return rtr;
	}

	@Override
	protected void visit(SequentialComposition c) {
		CodeBlock[] cb = c.getCodeBlocks();
		if (cb == null || cb.length == 0) {
			return;
		}
		visit(cb[cb.length - 1]);
	}

	@Override
	protected void visit(StatementSequence stmtSeq) {
		ReachDefStatementAnnotation annot = ReachDefStatementAnnotation.getAnnotation(
				stmtSeq.getStatements().get(stmtSeq.getStatements().size() - 1), mAnnotationSuffix);
		if (annot != null) {
			rtr.add(annot);
		}
		super.visit(stmtSeq);
	}
}
