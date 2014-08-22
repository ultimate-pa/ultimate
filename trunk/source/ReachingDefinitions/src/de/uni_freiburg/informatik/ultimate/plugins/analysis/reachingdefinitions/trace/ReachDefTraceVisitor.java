package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.trace;

import java.util.ArrayList;
import java.util.Collection;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ReachDefBoogieAnnotator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVarBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.util.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

/**
 * @author dietsch
 * 
 */
public class ReachDefTraceVisitor extends RCFGEdgeVisitor {

	private final Logger mLogger;
	private final CodeBlock mPredecessor;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mStatementProvider;
	private final IAnnotationProvider<ReachDefEdgeAnnotation> mEdgeProvider;
	private final ScopedBoogieVarBuilder mBuilder;

	public ReachDefTraceVisitor(IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider,
			IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider, CodeBlock predecessor, Logger logger,
			ScopedBoogieVarBuilder builder) {
		mLogger = logger;
		mPredecessor = predecessor;
		mStatementProvider = stmtProvider;
		mEdgeProvider = edgeProvider;
		mBuilder = builder;
	}

	public void process(CodeBlock e) {
		visit(e);
	}

	@Override
	protected void visit(CodeBlock c) {
		ReachDefEdgeAnnotation annot = mEdgeProvider.getAnnotation(c);
		if (annot == null) {
			annot = new ReachDefEdgeAnnotation(c, mStatementProvider);
			mEdgeProvider.annotate(c, annot);
		}
		super.visit(c);
	}

	@Override
	protected void visit(StatementSequence edge) {

		for (Statement s : edge.getStatements()) {
			ReachDefStatementAnnotation annot = mStatementProvider.getAnnotation(s);
			if (annot == null) {
				annot = new ReachDefStatementAnnotation();
				mStatementProvider.annotate(s, annot);
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
			predecessors.add((ReachDefStatementAnnotation) mStatementProvider.getAnnotation(currentSeq.getStatements()
					.get(currentIndex - 1)));
		} else if (mPredecessor != null) {
			// it is the first statement, we only need one predecessor
			// from the trace and only if this is not the first codeblock
			ReachDefTracePredecessorGenerator generator = new ReachDefTracePredecessorGenerator(mStatementProvider);
			predecessors = generator.process(mPredecessor);
		}

		return new ReachDefBoogieAnnotator(predecessors, stmtAnnotation, mStatementProvider, mLogger, mBuilder);
	}

}