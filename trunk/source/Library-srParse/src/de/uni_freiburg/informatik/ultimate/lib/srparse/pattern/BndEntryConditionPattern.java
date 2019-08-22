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
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlob;

/**
 * "{scope}, it is always the case that after "P" holds for "c1" time units, then "S" holds
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class BndEntryConditionPattern extends PatternType {

	public BndEntryConditionPattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public CounterTrace transform(final CDD[] cdds, final int[] durations) {
		assert cdds.length == 2 && durations.length == 1;

		final SrParseScope scope = getScope();
		// note: Q and R are reserved for scope, cdds are parsed in reverse order
		final CDD P = cdds[1];
		final CDD S = cdds[0];
		final int c1 = durations[0];

		final CounterTrace ct;
		if (scope instanceof SrParseScopeGlob) {
			ct = counterTrace(phaseT(), phase(P, BoundTypes.GREATER, c1), phase(S.negate()), phaseT());
		} else if (scope instanceof SrParseScopeBefore) {
			final CDD R = scope.getCdd2();
			ct = counterTrace(phase(R.negate()), phase(P.and(R.negate()), BoundTypes.GREATER, c1),
					phase(S.negate().and(R.negate())), phaseT());
		} else if (scope instanceof SrParseScopeAfterUntil) {
			final CDD Q = scope.getCdd1();
			final CDD R = scope.getCdd2();
			ct = counterTrace(phaseT(), phase(Q.and(R.negate())), phase(R.negate()),
					phase(P.and(R.negate()), BoundTypes.GREATER, c1), phase(S.negate().and(R.negate())), phaseT());
		} else if (scope instanceof SrParseScopeAfter) {
			final CDD Q = scope.getCdd1();
			ct = counterTrace(phaseT(), phase(Q), phaseT(), phase(P, BoundTypes.GREATER, c1), phase(S.negate()),
					phaseT());
		} else if (scope instanceof SrParseScopeBetween) {
			final CDD Q = scope.getCdd1();
			final CDD R = scope.getCdd2();
			ct = counterTrace(phaseT(), phase(Q.and(R.negate())), phase(R.negate()),
					phase(P.and(R.negate()), BoundTypes.GREATER, c1), phase(S.negate().and(R.negate())),
					phase(R.negate()), phase(R), phaseT());
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
		sb.append("it is always the case that after \"");
		sb.append(getCdds().get(1).toBoogieString());
		sb.append("\" holds for \"");
		sb.append(getDuration().get(0));
		sb.append("\" time units, then \"");
		sb.append(getCdds().get(0).toBoogieString());
		sb.append("\" holds");
		return sb.toString();
	}

	@Override
	public PatternType rename(final String newName) {
		return new BndEntryConditionPattern(getScope(), newName, getCdds(), getDuration());
	}
}
