package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;

public class TwoTrackInterpolantAutomatonBuilder {
	
	private final TraceCheckerSpWp m_TraceCheckerSpWp;
	
	private NestedWordAutomaton<CodeBlock, IPredicate> m_Result;
	
	public TwoTrackInterpolantAutomatonBuilder(
			IRun<CodeBlock,IPredicate> nestedRun,
			TraceChecker traceChecker) {
		if (!(traceChecker instanceof TraceCheckerSpWp)) {
			throw new UnsupportedOperationException("Wrong trace checker");
		}
		m_TraceCheckerSpWp = (TraceCheckerSpWp) traceChecker;
	}
	
	
	
	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return m_Result;
	}

}
