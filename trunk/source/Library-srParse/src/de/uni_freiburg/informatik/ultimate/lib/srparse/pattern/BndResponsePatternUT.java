package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.BoundTypes;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PatternToPEA;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfterUntil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBetween;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlob;

/**
 * {scope}, it is always the case that if "R" holds, then "S" holds after at most "c1" time units.
 *
 * @author Amalinda Post
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class BndResponsePatternUT extends PatternType {
	public BndResponsePatternUT(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public PhaseEventAutomata transform(final PatternToPEA peaTrans, final Map<String, Integer> id2bounds) {
		final CDD[] cdds = getCddsAsArray();
		final int[] durations = getDurationsAsIntArray(id2bounds);
		assert cdds.length == 2 && durations.length == 1;

		final SrParseScope scope = getScope();
		// note: P and Q are reserved for scope, cdds are parsed in reverse order
		final CDD R = cdds[1];
		final CDD S = cdds[0];
		final int c1 = durations[0];

		if (scope instanceof SrParseScopeGlob) {
			final CounterTrace ct = counterTrace(phaseT(), phase(R.and(S.negate())),
					phase(S.negate(), BoundTypes.GREATER, c1), phaseT());
			return compile(peaTrans, ct);
		} else if (scope instanceof SrParseScopeBefore) {
			final CDD P = scope.getCdd1();
			final CounterTrace ct = counterTrace(phase(P.negate()), phase(P.negate().and(R).and(S.negate())),
					phase(S.negate().and(P.negate()), BoundTypes.GREATEREQUAL, c1), phaseT());
			return compile(peaTrans, ct);
		} else if (scope instanceof SrParseScopeAfterUntil) {
			final CDD P = scope.getCdd1();
			final CDD Q = scope.getCdd2();
			final CounterTrace ct = counterTrace(phaseT(), phase(P.and(Q.negate())), phase(Q.negate()),
					phase(R.and(Q.negate()).and(S.negate())),
					phase(S.negate().and(Q.negate()), BoundTypes.GREATEREQUAL, c1), phaseT());
			return compile(peaTrans, ct);
		} else if (scope instanceof SrParseScopeAfter) {
			final CDD P = scope.getCdd1();
			final CounterTrace ct = counterTrace(phaseT(), phase(P), phaseT(), phase(R.and(S.negate())),
					phase(S.negate(), BoundTypes.GREATEREQUAL, c1), phaseT());
			return compile(peaTrans, ct);
		} else if (scope instanceof SrParseScopeBetween) {
			final CDD P = scope.getCdd1();
			final CDD Q = scope.getCdd2();
			final CounterTrace ct = counterTrace(phaseT(), phase(P.and(Q.negate())), phase(Q.negate()),
					phase(R.and(Q.negate()).and(S.negate())),
					phase(S.negate().and(Q.negate()), BoundTypes.GREATEREQUAL, c1), phase(Q.negate()), phase(Q),
					phaseT());
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
		sb.append("it is always the case that if \"");
		sb.append(getCdds().get(1).toBoogieString());
		sb.append("\" holds, then \"");
		sb.append(getCdds().get(0).toBoogieString());
		sb.append("\" holds after at most \"");
		sb.append(getDuration().get(0));
		sb.append("\" time units");
		return sb.toString();
	}

	@Override
	public PatternType rename(final String newName) {
		return new BndResponsePatternUT(getScope(), newName, getCdds(), getDuration());
	}
}
