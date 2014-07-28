package de.uni_freiburg.informatik.ultimate.reachingdefinitions.rcfg;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.util.Util;

public class ReachDefRCFGPredecessorGenerator extends RCFGEdgeVisitor {

	private final Logger mLogger;
	private final String mAnnotationSuffix;

	public ReachDefRCFGPredecessorGenerator(String annotationSuffix, Logger logger) {
		mLogger = logger;
		mAnnotationSuffix = annotationSuffix;
	}

	private List<ReachDefStatementAnnotation> rtr;

	/**
	 * Returns all preceeding {@link ReachDefStatementAnnotation}s
	 * 
	 * @param e
	 * @return
	 */
	public List<ReachDefStatementAnnotation> process(RCFGNode currentNode) {
		rtr = new ArrayList<ReachDefStatementAnnotation>();
		if (currentNode == null) {
			return rtr;
		}

		for (RCFGEdge pre : currentNode.getIncomingEdges()) {
			visit(pre);
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Predecessors: "
					+ Util.prettyPrintIterable(currentNode.getIncomingEdges(), Util.<RCFGEdge> createHashCodePrinter()));
		}

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
