package de.uni_freiburg.informatik.ultimate.reachingdefinitions.trace;

import java.util.ArrayList;
import java.util.Collection;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.boogie.ReachDefBoogieAnnotator;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.util.Util;

/**
 * @author dietsch
 * 
 */
public class ReachDefTraceVisitor extends RCFGEdgeVisitor {

	private final Logger mLogger;
	private final String mAnnotationSuffix;
	private final CodeBlock mPredecessor;

	public ReachDefTraceVisitor(String annotationSuffix, CodeBlock predecessor, Logger logger) {
		mLogger = logger;
		mAnnotationSuffix = annotationSuffix;
		mPredecessor = predecessor;
	}

	public void process(CodeBlock e) {
		visit(e);
	}

	@Override
	protected void visit(CodeBlock c) {
		ReachDefEdgeAnnotation annot = ReachDefEdgeAnnotation.getAnnotation(c, mAnnotationSuffix);
		if (annot == null) {
			annot = new ReachDefEdgeAnnotation(c, mAnnotationSuffix);
			annot.annotate(c, mAnnotationSuffix);
		}
		super.visit(c);
	}

	@Override
	protected void visit(StatementSequence edge) {

		for (Statement s : edge.getStatements()) {
			ReachDefStatementAnnotation annot = ReachDefStatementAnnotation.getAnnotation(s, mAnnotationSuffix);
			if (annot == null) {
				annot = new ReachDefStatementAnnotation();
				annot.annotate(s, mAnnotationSuffix);
			}
			ReachDefBoogieAnnotator generator = createBoogieAnnotator(edge, s, annot);
			try {
				generator.annotate(s);
				String pre = " 		      " + edge.hashCode() + " " + BoogieStatementPrettyPrinter.print(s);

				if (mLogger.isDebugEnabled()) {
					mLogger.debug(pre + Util.repeat((40 - pre.length()), " ") + " New: " + annot);
				}
			} catch (Throwable e) {
				// Fail fast after fatal error
				mLogger.fatal("Fatal error occured", e);
				return;
			}
		}
		super.visit(edge);
	}

	private ReachDefBoogieAnnotator createBoogieAnnotator(StatementSequence currentSeq, Statement currentStmt,
			ReachDefStatementAnnotation stmtAnnotation) {

		Collection<ReachDefStatementAnnotation> predecessors;

		int currentIndex = currentSeq.getStatements().indexOf(currentStmt);
		predecessors = new ArrayList<>();

		if (currentIndex != 0) {
			// its not the first statement, so we only need the straight line
			// predecessor
			predecessors.add((ReachDefStatementAnnotation) ReachDefStatementAnnotation.getAnnotation(currentSeq
					.getStatements().get(currentIndex - 1), mAnnotationSuffix));
		} else if (mPredecessor != null) {
			// it is the first statement, we only need one predecessor
			// from the trace and only if this is not the first codeblock
			ReachDefTracePredecessorGenerator generator = new ReachDefTracePredecessorGenerator(mAnnotationSuffix);
			predecessors = generator.process(mPredecessor);
		}

		return new ReachDefBoogieAnnotator(predecessors, stmtAnnotation, mAnnotationSuffix, mLogger);
	}

}