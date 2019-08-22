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
 * {scope}, it is always the case that if "P" holds, then "S", previously held and was preceded by "T"
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PrecedenceChain21Pattern extends PatternType {

	public PrecedenceChain21Pattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public CounterTrace transform(final CDD[] cdds, final int[] durations) {
		assert cdds.length == 3;

		final SrParseScope scope = getScope();
		// note: Q and R are reserved for scope, cdds are parsed in reverse order
		final CDD P = cdds[2];
		final CDD S = cdds[1];
		final CDD T = cdds[0];

		// final CDD Q = scope.getCdd1();
		// final CDD R = scope.getCdd2();

		final CounterTrace ct;
		if (scope instanceof SrParseScopeGlob) {
			ct = counterTrace(phase(S.negate()), phase(S.and(T.negate())), phase(T.negate()), phase(P), phaseT());
		} else if (scope instanceof SrParseScopeBefore) {
			ct = counterTrace(phaseT());
			throw new PatternScopeNotImplemented(scope.getClass(), getClass());
		} else if (scope instanceof SrParseScopeAfterUntil) {
			ct = counterTrace(phaseT());
			throw new PatternScopeNotImplemented(scope.getClass(), getClass());
		} else if (scope instanceof SrParseScopeAfter) {
			ct = counterTrace(phaseT());
			throw new PatternScopeNotImplemented(scope.getClass(), getClass());
		} else if (scope instanceof SrParseScopeBetween) {
			ct = counterTrace(phaseT());
			throw new PatternScopeNotImplemented(scope.getClass(), getClass());
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
		sb.append(getCdds().get(2).toBoogieString());
		sb.append("\" holds, then \"");
		sb.append(getCdds().get(1).toBoogieString());
		sb.append("\", previously held and was preceded by \"");
		sb.append(getCdds().get(0).toBoogieString());
		sb.append("\"");
		return sb.toString();
	}

	@Override
	public PatternType rename(final String newName) {
		return new PrecedenceChain21Pattern(getScope(), newName, getCdds(), getDuration());
	}
}
