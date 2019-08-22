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
 * "{scope}, it is always the case that if "P" holds, then "S" eventually holds"
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ResponsePattern extends PatternType {
	public ResponsePattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public CounterTrace transform(final CDD[] cdds, final int[] durations) {
		assert cdds.length == 2;

		final SrParseScope scope = getScope();
		// note: Q and R are reserved for scope, cdds are parsed in reverse order
		final CDD S = cdds[0];
		final CDD P = cdds[1];

		final CounterTrace ct;

		if (scope instanceof SrParseScopeGlob) {
			// Globally, it is always the case that if P holds then S eventually holds.
			// (¬(true;|P ∧ ¬S|;|¬S|)) -> true
			// TODO: Amalinda schrieb: hier brauchen wir einen anderen Mechanismus denn S.negate müßte bis zum ende des
			// intervalls gelten
			// TODO: Das leads-to scheint falsch
			ct = counterTrace(phaseT(), phase(P.and(S.negate())), phase(S.negate()), phaseT());
		} else if (scope instanceof SrParseScopeBefore) {
			// Before Q, it is always the case that if P holds then S eventually holds.
			// ¬(|¬Q|;|P ∧ ¬S ∧ ¬Q|;|¬S ∧ ¬Q|;|Q|; true)
			final CDD R = scope.getCdd2();
			ct = counterTrace(phase(R.negate()), phase(P.and(R.negate()).and(S.negate())),
					phase(S.negate().and(R.negate())), phase(R), phaseT());
		} else if (scope instanceof SrParseScopeAfterUntil) {
			// TODO: Amalinda schrieb: hier brauchen wir einen anderen Mechanismus denn S.negate müßte bis zum ende des
			// intervalls gelten
			ct = counterTrace(phaseT());
			throw new PatternScopeNotImplemented(scope.getClass(), getClass());
		} else if (scope instanceof SrParseScopeAfter) {
			// (¬(true;|Q|;true;|P ∧ ¬S|;|¬S|)) -> true
			// TODO: Amalinda schrieb: hier brauchen wir einen anderen Mechanismus denn S.negate müßte bis zum ende des
			// intervalls gelten
			ct = counterTrace(phaseT());
			throw new PatternScopeNotImplemented(scope.getClass(), getClass());
		} else if (scope instanceof SrParseScopeBetween) {
			final CDD Q = scope.getCdd1();
			final CDD R = scope.getCdd2();
			ct = counterTrace(phaseT(), phase(Q.and(R.negate())), phase(R.negate()),
					phase(P.and(R.negate()).and(S.negate())), phase(R.negate().and(S.negate())), phase(R), phaseT());
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
		sb.append("\" eventually holds");
		return sb.toString();
	}

	@Override
	public PatternType rename(final String newName) {
		return new ResponsePattern(getScope(), newName, getCdds(), getDuration());
	}
}
