package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.TracePredicates;

public class InterpolantSequences {
	public static InterpolantSequences instance = new InterpolantSequences();
	
	public List<TracePredicates> mPerfectIpps;
	public List<TracePredicates> mImperfectIpps;

	public InterpolantSequences set(final List<TracePredicates> perfectIpps,
			final List<TracePredicates> imperfectIpps) {
		mPerfectIpps = perfectIpps;
		mImperfectIpps = imperfectIpps;
		return this;
	}
}
