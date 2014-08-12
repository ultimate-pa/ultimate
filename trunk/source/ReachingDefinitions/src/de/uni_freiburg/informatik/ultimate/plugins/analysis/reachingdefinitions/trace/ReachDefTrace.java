package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.trace;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class ReachDefTrace {

	private final Logger mLogger;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mStatementProvider;
	private final IAnnotationProvider<ReachDefEdgeAnnotation> mEdgeProvider;

	public ReachDefTrace(IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider,
			IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider, Logger logger) {
		mLogger = logger;
		mStatementProvider = stmtProvider;
		mEdgeProvider = edgeProvider;
	}

	public void process(CodeBlock[] trace) throws Throwable {
		for (int i = 0; i < trace.length; i++) {
			ReachDefTraceVisitor v;
			if (i == 0) {
				v = new ReachDefTraceVisitor(mStatementProvider, mEdgeProvider, null, mLogger);
			} else {
				v = new ReachDefTraceVisitor(mStatementProvider, mEdgeProvider, trace[i - 1], mLogger);
			}
			v.process(trace[i]);
		}
	}

}
