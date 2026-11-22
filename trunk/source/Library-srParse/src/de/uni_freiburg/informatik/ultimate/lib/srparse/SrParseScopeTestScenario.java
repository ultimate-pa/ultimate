package de.uni_freiburg.informatik.ultimate.lib.srparse;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

/**
 * "TestScenario for <ID | ALL>, ..." - scope of a TestScenario pattern. Carries the target: a requirement id or "ALL".
 * Which requirements the trace is actually checked against is decided in Req2BoogieTranslator.
 */
public class SrParseScopeTestScenario extends SrParseScope<SrParseScopeTestScenario> {

	private final String mTargetReqId;

	public SrParseScopeTestScenario(final String targetReqId) {
		super(null, null);
		mTargetReqId = targetReqId;
	}

	public String getTargetReqId() {
		return mTargetReqId;
	}

	@Override
	public SrParseScopeTestScenario create(final CDD cdd1, final CDD cdd2) {
		return new SrParseScopeTestScenario(mTargetReqId);
	}

	@Override
	public String toString() {
		return "TestScenario for " + mTargetReqId + ", ";
	}

	@Override
	public int hashCode() {
		return Objects.hash(super.hashCode(), mTargetReqId);
	}

	@Override
	public boolean equals(final Object obj) {
		return super.equals(obj) && Objects.equals(mTargetReqId, ((SrParseScopeTestScenario) obj).mTargetReqId);
	}
}
