package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfterUntil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBetween;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlob;

/**
 * {scope}, it is always the case that if "P" holds, then "S", previously held
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PrecedencePattern extends PatternType {

	public PrecedencePattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public CounterTrace transform(final CDD[] cdds, final int[] durations) {
		assert cdds.length == 1;

		final SrParseScope scope = getScope();
		// note: Q and R are reserved for scope, cdds are parsed in reverse order
		final CDD P = cdds[1];
		final CDD S = cdds[0];

		final CounterTrace ct;
		if (scope instanceof SrParseScopeGlob) {
			ct = counterTrace(phase(S.negate()), phase(P), phaseT());
		} else if (scope instanceof SrParseScopeBefore) {
			final CDD R = scope.getCdd2();
			ct = counterTrace(phase(R.negate().and(S.negate())), phase(P.and(R.negate())), phaseT());
		} else if (scope instanceof SrParseScopeAfterUntil) {
			final CDD Q = scope.getCdd1();
			final CDD R = scope.getCdd2();
			ct = counterTrace(phaseT(), phase(Q.and(R.negate()).and(S.negate())), phase(S.negate().and(R.negate())),
					phase(P.and(R.negate())), phaseT());
		} else if (scope instanceof SrParseScopeAfter) {
			final CDD Q = scope.getCdd1();
			ct = counterTrace(phaseT(), phase(Q.and(S.negate())), phase(S.negate()), phase(P), phaseT());
		} else if (scope instanceof SrParseScopeBetween) {
			final CDD Q = scope.getCdd1();
			final CDD R = scope.getCdd2();
			ct = counterTrace(phaseT(), phase(Q.and(S.negate()).and(R.negate())), phase(S.negate().and(R.negate())),
					phase(P.and(R.negate()).and(S.negate())), phase(R.negate()), phase(R), phaseT());
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
		sb.append("it is always the case that if \"");
		sb.append(getCdds().get(1).toBoogieString());
		sb.append("\" holds, then \"");
		sb.append(getCdds().get(0).toBoogieString());
		sb.append("\", previously held");
		return sb.toString();
	}

	@Override
	public PatternType rename(final String newName) {
		return new PrecedencePattern(getScope(), newName, getCdds(), getDuration());
	}
}
