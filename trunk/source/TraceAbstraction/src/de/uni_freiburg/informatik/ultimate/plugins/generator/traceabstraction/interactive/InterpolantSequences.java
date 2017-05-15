package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;

public class InterpolantSequences {
	public static InterpolantSequences instance = new InterpolantSequences();
	
	public List<InterpolantsPreconditionPostcondition> mPerfectIpps;
	public List<InterpolantsPreconditionPostcondition> mImperfectIpps;

	public InterpolantSequences set(final List<InterpolantsPreconditionPostcondition> perfectIpps,
			final List<InterpolantsPreconditionPostcondition> imperfectIpps) {
		mPerfectIpps = perfectIpps;
		mImperfectIpps = imperfectIpps;
		return this;
	}
}
