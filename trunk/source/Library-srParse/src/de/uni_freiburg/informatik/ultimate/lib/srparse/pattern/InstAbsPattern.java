package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfterUntil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBetween;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlob;

/**
 * {scope}, it is never the case that "P" holds
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class InstAbsPattern extends PatternType {
	public InstAbsPattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public CounterTrace transform(final CDD[] cdds, final int[] durations) {
		assert cdds.length == 1 && durations.length == 0;

		final SrParseScope scope = getScope();

		// note: Q and R are reserved for scope, cdds are parsed in reverse order
		final CDD P = cdds[0];

		final CDD Q = scope.getCdd1();
		final CDD R = scope.getCdd2();

		final CounterTrace ct;
		if (scope instanceof SrParseScopeGlob) {
			ct = counterTrace(phaseT(), phase(P), phaseT());
		} else if (scope instanceof SrParseScopeAfterUntil) {
			ct = counterTrace(phaseT(), phase(Q.and(R.negate())), phase(R.negate()), phase(P.and(R.negate())),
					phaseT());
		} else if (scope instanceof SrParseScopeAfter) {
			ct = counterTrace(phaseT(), phase(Q), phaseT(), phase(P), phaseT());
		} else if (scope instanceof SrParseScopeBetween) {
			ct = counterTrace(phaseT(), phase(Q.and(R.negate())), phase(R.negate()), phase(P.and(R.negate())),
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
		sb.append("it is never the case that \"");
		sb.append(getCdds().get(0).toBoogieString());
		sb.append("\" holds");
		return sb.toString();
	}

	@Override
	public PatternType rename(final String newName) {
		return new InstAbsPattern(getScope(), newName, getCdds(), getDuration());
	}
}
