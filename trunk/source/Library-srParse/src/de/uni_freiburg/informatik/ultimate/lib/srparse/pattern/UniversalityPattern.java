package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PatternToPEA;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfterUntil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBetween;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlob;

/**
 * {scope}, it is always the case that "S" holds.
 *
 * @author Amalinda Post
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class UniversalityPattern extends PatternType {

	public UniversalityPattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public PhaseEventAutomata transform(final PatternToPEA peaTrans, final Map<String, Integer> id2bounds) {
		final CDD[] cdds = getCddsAsArray();
		final int[] durations = getDurationsAsIntArray(id2bounds);
		assert cdds.length == 1 && durations.length == 0;

		final SrParseScope scope = getScope();
		final CDD S = cdds[0];

		if (scope instanceof SrParseScopeGlob) {
			final CounterTrace ct = counterTrace(phaseT(), phase(S.negate()), phaseT());
			return compile(peaTrans, ct);
		} else if (scope instanceof SrParseScopeBefore) {
			final CDD P = scope.getCdd1();
			final CounterTrace ct = counterTrace(phase(P.negate()), phase(S.negate().and(P.negate())), phaseT());
			return compile(peaTrans, ct);
		} else if (scope instanceof SrParseScopeAfterUntil) {
			final CDD P = scope.getCdd1();
			final CDD Q = scope.getCdd2();
			final CounterTrace ct = counterTrace(phaseT(), phase(P.and(Q.negate())), phase(Q.negate()),
					phase(S.negate().and(Q.negate())), phaseT());
			return compile(peaTrans, ct);
		} else if (scope instanceof SrParseScopeAfter) {
			final CDD P = scope.getCdd1();
			final CounterTrace ct = counterTrace(phaseT(), phase(P), phaseT(), phase(S.negate()), phaseT());
			return compile(peaTrans, ct);
		} else if (scope instanceof SrParseScopeBetween) {
			final CDD P = scope.getCdd1();
			final CDD Q = scope.getCdd2();
			final CounterTrace ct = counterTrace(phaseT(), phase(P.and(Q.negate())), phase(Q.negate()),
					phase(S.negate().and(Q.negate())), phase(Q.negate()), phase(Q), phaseT());
			return compile(peaTrans, ct);
		} else {
			throw new PatternScopeNotImplemented(scope.getClass(), getClass());
		}
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
		sb.append("it is always the case that \"");
		sb.append(getCdds().get(0).toBoogieString());
		sb.append("\" holds");
		return sb.toString();
	}

	@Override
	public PatternType rename(final String newName) {
		return new UniversalityPattern(getScope(), newName, getCdds(), getDuration());
	}
}
