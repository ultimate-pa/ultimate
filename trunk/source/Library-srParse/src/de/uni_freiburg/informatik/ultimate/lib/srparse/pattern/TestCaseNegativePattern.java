package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * {scope}, TestCase for R1, trace is forbidden to hold: (c1, expr1), (c2, expr2), ...
 *
 * Counterpart of {@link TestCasePositivePattern} for "is forbidden to hold" - see that class for the rationale.
 */
public class TestCaseNegativePattern extends PatternType<TestCaseNegativePattern> {

	private final String mTargetReqId;

	public TestCaseNegativePattern(final SrParseScope<?> scope, final String id, final List<CDD> cdds,
			final List<Rational> durations, final List<String> durationNames, final String targetReqId) {
		super(scope, id, cdds, durations, durationNames);
		mTargetReqId = targetReqId;
	}

	public String getTargetReqId() {
		return mTargetReqId;
	}

	@Override
	public TestCaseNegativePattern create(final SrParseScope<?> scope, final String id, final List<CDD> cdds,
			final List<Rational> durations, final List<String> durationNames) {
		return new TestCaseNegativePattern(scope, id, cdds, durations, durationNames, mTargetReqId);
	}

	@Override
	public TestCaseNegativePattern rename(final String newName) {
		return new TestCaseNegativePattern(getScope(), newName, getCdds(), getDurations(), getDurationNames(),
				mTargetReqId);
	}

	@Override
	public List<CounterTrace> transform(final CDD[] cdds, final int[] durations) {
		return Collections.emptyList();
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		if (getId() != null) {
			sb.append(getId());
			sb.append(": ");
		}
		if (getScope() != null) {
			sb.append(getScope());
		}
		sb.append("TestCase trace is forbidden to hold: ");
		appendTrace(sb);
		return sb.toString();
	}

	private void appendTrace(final StringBuilder sb) {
		final List<CDD> cdds = getCdds();
		final List<Rational> durations = getDurations();
		for (int i = 0; i < cdds.size(); ++i) {
			if (i > 0) {
				sb.append(", ");
			}
			sb.append('(').append(durations.get(i)).append(", ").append(cdds.get(i).toBoogieString()).append(')');
		}
	}

	@Override
	public int getExpectedCddSize() {
		return getCdds().size();
	}

	@Override
	public int getExpectedDurationSize() {
		return getDurations().size();
	}
}