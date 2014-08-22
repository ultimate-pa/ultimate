package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.trace;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVarBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class ReachDefTrace {

	private final Logger mLogger;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mStatementProvider;
	private final IAnnotationProvider<ReachDefEdgeAnnotation> mEdgeProvider;
	private final BoogieSymbolTable mSymbolTable;

	public ReachDefTrace(IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider,
			IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider, Logger logger, BoogieSymbolTable symboltable) {
		mLogger = logger;
		mStatementProvider = stmtProvider;
		mEdgeProvider = edgeProvider;
		mSymbolTable = symboltable;
	}

	public void process(CodeBlock[] trace) throws Throwable {
		for (int i = 0; i < trace.length; i++) {
			CodeBlock current = null;
			if (i != 0) {
				current = trace[i - 1];
			}
			
			new ReachDefTraceVisitor(mStatementProvider, mEdgeProvider, current, mLogger, new ScopedBoogieVarBuilder(mSymbolTable))
					.process(trace[i]);
		}
	}

}
