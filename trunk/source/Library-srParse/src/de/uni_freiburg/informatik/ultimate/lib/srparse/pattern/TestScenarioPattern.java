package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeTestScenario;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * TestScenario for <ID | ALL>, trace has to hold / is forbidden to hold: (c1, expr1), (c2, expr2), ...
 *
 * Describes one concrete timed trace and whether the requirements must allow it ("has to hold") or must exclude it
 * ("is forbidden to hold"). It is not a requirement: no PEA is built for it, Req2BoogieTranslator encodes the trace
 * directly as assume statements.
 *
 * The target ({@link SrParseScopeTestScenario}) is a requirement id or "ALL". Which requirements the trace is checked
 * against is decided in Req2BoogieTranslator: all of them for "ALL", for an unknown id, or if the preference
 * "TestScenarios test the whole graph" is on; otherwise the requirement with that id and its formalizations id_*.
 */
public abstract class TestScenarioPattern<T extends TestScenarioPattern<?>> extends PatternType<T> {

	protected TestScenarioPattern(final SrParseScope<?> scope, final String id, final List<CDD> cdds,
			final List<Rational> durations, final List<String> durationNames) {
		super(scope, id, cdds, durations, durationNames);
	}

	/**
	 * @return "has to hold" or "is forbidden to hold"
	 */
	protected abstract String getModality();

	public String getTargetReqId() {
		return ((SrParseScopeTestScenario) getScope()).getTargetReqId();
	}

	@Override
	public List<CounterTrace> transform(final CDD[] cdds, final int[] durations) {
		return Collections.emptyList();
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getId()).append(": ").append(getScope()).append("trace ").append(getModality()).append(": ");
		final List<CDD> cdds = getCdds();
		for (int i = 0; i < cdds.size(); ++i) {
			if (i > 0) {
				sb.append(", ");
			}
			sb.append('(').append(getDurations().get(i)).append(", ").append(cdds.get(i).toBoogieString()).append(')');
		}
		return sb.toString();
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
