package de.uni_freiburg.informatik.ultimate.lib.srparse;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

/**
 * "TestCase for [ID], ..." - scope of a TestCase pattern, carries the requirement the test case is checked against.
 */
public class SrParseScopeTestCase extends SrParseScope<SrParseScopeTestCase> {

	private final String mTargetReqId;

	public SrParseScopeTestCase(final String targetReqId) {
		super(null, null);
		mTargetReqId = targetReqId;
	}

	public String getTargetReqId() {
		return mTargetReqId;
	}

	@Override
	public SrParseScopeTestCase create(final CDD cdd1, final CDD cdd2) {
		return new SrParseScopeTestCase(mTargetReqId);
	}

	@Override
	public String toString() {
		return "TestCase for " + mTargetReqId + ", ";
	}

	@Override
	public int hashCode() {
		return Objects.hash(super.hashCode(), mTargetReqId);
	}

	@Override
	public boolean equals(final Object obj) {
		return super.equals(obj) && Objects.equals(mTargetReqId, ((SrParseScopeTestCase) obj).mTargetReqId);
	}
}
