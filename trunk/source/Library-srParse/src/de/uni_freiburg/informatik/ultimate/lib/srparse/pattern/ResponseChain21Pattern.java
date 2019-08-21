package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PatternToPEA;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;

/**
 * TODO: fix description
 *
 * {scope}, it is always the case that if "" holds and is succeeded by "P", then "S" eventually holds after "T"
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ResponseChain21Pattern extends PatternType {
	public ResponseChain21Pattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public PhaseEventAutomata transform(final PatternToPEA peaTrans, final Map<String, Integer> id2bounds) {
		// TODO: Complete refactoring
		// final CDD[] cdds = getCddsAsArray();
		// assert cdds.length == 3
		//
		// final SrParseScope scope = getScope();
		// final CDD P = cdds[2];
		// final CDD S = cdds[1];
		// final CDD T = cdds[0];
		//
		// final CounterTrace ct;
		//
		// if (scope instanceof SrParseScopeGlob) {
		// ct = counterTrace(phaseT());
		// } else if (scope instanceof SrParseScopeBefore) {
		// final CDD Q = scope.getCdd1();
		// final CDD R = scope.getCdd2();
		// ct = counterTrace(phase(R.negate()), phase(S.and(R.negate()).and(T.negate())), phase(R.negate()),
		// phase(T.and(R.negate())), phase(P.negate().and(R.negate())), phase(R), phaseT());
		// } else if (scope instanceof SrParseScopeAfterUntil) {
		// ct = counterTrace(phaseT());
		// } else if (scope instanceof SrParseScopeAfter) {
		// ct = counterTrace(phaseT());
		// } else if (scope instanceof SrParseScopeBetween) {
		// final CDD Q = scope.getCdd1();
		// final CDD R = scope.getCdd2();
		// ct = counterTrace(phaseT(), phase(Q.and(R.negate())), phase(R.negate()),
		// phase(S.and(R.negate()).and(T.negate())), phase(R.negate()), phase(T.and(R.negate())),
		// phase(P.negate().and(R.negate())), phase(R), phaseT());
		// } else {
		// throw new PatternScopeNotImplemented(scope.getClass(), getClass());
		// }
		//
		// return compile(peaTrans, ct);

		final CDD p_cdd = getCdds().get(2);
		final CDD q_cdd = getScope().getCdd1();
		final CDD r_cdd = getScope().getCdd2();
		final CDD s_cdd = getCdds().get(1);
		final CDD t_cdd = getCdds().get(0);

		// Klappt noch gar nicht
		return peaTrans.responseChainPattern21(getId(), p_cdd, q_cdd, r_cdd, s_cdd, t_cdd, getScope().toString());
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
		sb.append(getCdds().get(3).toBoogieString());
		sb.append("\" holds and is succeeded by \"");
		sb.append(getCdds().get(2).toBoogieString());
		sb.append("\", then \"");
		sb.append(getCdds().get(1).toBoogieString());
		sb.append("\" eventually holds after \"");
		sb.append(getCdds().get(0).toBoogieString());
		sb.append("\"");
		return sb.toString();
	}

	@Override
	public PatternType rename(final String newName) {
		return new ResponseChain21Pattern(getScope(), newName, getCdds(), getDuration());
	}
}
