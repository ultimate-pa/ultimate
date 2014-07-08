package de.uni_freiburg.informatik.ultimate.reachingdefinitions.trace;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class ReachDefTrace {

	private final static String sAnnotationSuffix = "Trace"; 
	
	public void process(CodeBlock[] trace) throws Throwable {
		for (int i = 0; i < trace.length; i++) {
			ReachDefTraceVisitor v;
			if (i == 0) {
				v = new ReachDefTraceVisitor(sAnnotationSuffix, null);
			} else {
				v = new ReachDefTraceVisitor(sAnnotationSuffix, trace[i - 1]);
			}
			v.process(trace[i]);
		}
	}

}
