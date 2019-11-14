package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.BoundTypes;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfterUntil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBetween;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlobally;

/**
 * {scope}, it is always the case that once "P" becomes satisfied, it holds for at least "c1" time units
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class MinDurationPattern extends PatternType {
	public MinDurationPattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public CounterTrace transform(final CDD[] cdds, final int[] durations) {
		final SrParseScope scope = getScope();
		// note: Q and R are reserved for scope, cdds are parsed in reverse order
		final CDD P = cdds[0];
		final int c1 = durations[0];

		final CounterTrace ct;
		if (scope instanceof SrParseScopeGlobally) {
			ct = counterTrace(phaseT(), phase(P.negate()), phase(P, BoundTypes.LESS, c1), phase(P.negate()), phaseT());
		} else if (scope instanceof SrParseScopeBefore) {
			final CDD Q = scope.getCdd1();
			ct = counterTrace(phase(Q.negate()), phase(Q.negate().and(P.negate())),
					phase(P.and(Q.negate()), BoundTypes.LESS, c1), phase(Q.negate().and(P.negate())), phaseT());
		} else if (scope instanceof SrParseScopeAfterUntil) {
			final CDD Q = scope.getCdd1();
			final CDD R = scope.getCdd2();
			ct = counterTrace(phaseT(), phase(Q.and(R.negate())), phase(R.negate()), phase(P.negate().and(R.negate())),
					phase(P.and(R.negate()), BoundTypes.LESS, c1), phase(R.negate().and(P.negate())), phaseT());
		} else if (scope instanceof SrParseScopeAfter) {
			final CDD Q = scope.getCdd1();
			ct = counterTrace(phaseT(), phase(Q), phaseT(), phase(P.negate()), phase(P, BoundTypes.LESS, c1),
					phase(P.negate()), phaseT());
		} else if (scope instanceof SrParseScopeBetween) {
			final CDD Q = scope.getCdd1();
			final CDD R = scope.getCdd2();
			ct = counterTrace(phaseT(), phase(Q.and(R.negate())), phase(R.negate()), phase(P.negate().and(R.negate())),
					phase(P.and(R.negate()), BoundTypes.LESS, c1), phase(R.negate().and(P.negate())), phase(R.negate()),
					phase(R), phaseT());
		} else {
			throw new PatternScopeNotImplemented(scope.getClass(), getClass());
		}

		return ct;
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
		sb.append("it is always the case that once \"");
		sb.append(getCdds().get(0).toBoogieString());
		sb.append("\" becomes satisfied, it holds for at least \"");
		sb.append(getDuration().get(0));
		sb.append("\" time units");
		return sb.toString();
	}

	@Override
	public PatternType rename(final String newName) {
		return new MinDurationPattern(getScope(), newName, getCdds(), getDuration());
	}

	@Override
	public int getExpectedCddSize() {
		return 1;
	}

	@Override
	public int getExpectedDurationSize() {
		return 1;
	}
}
