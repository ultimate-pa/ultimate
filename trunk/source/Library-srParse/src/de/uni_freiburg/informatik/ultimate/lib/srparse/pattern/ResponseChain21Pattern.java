package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBetween;

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
	public CounterTrace transform(CDD[] cdds, int[] durations) {
		final SrParseScope scope = getScope();
		final CDD P = getCdds().get(2);
		final CDD R = scope.getCdd2();
		final CDD S = getCdds().get(1);
		final CDD T = getCdds().get(0);

		if (scope instanceof SrParseScopeBefore) {
			final CounterTrace ct = counterTrace(phase(R.negate()), phase(S.and(R.negate()).and(T.negate())),
					phase(R.negate()), phase(T.and(R.negate())), phase(P.negate().and(R.negate())), phase(R), phaseT());

			return ct;
		} else if (scope instanceof SrParseScopeBetween) {
			final CDD Q = getScope().getCdd1();
			final CounterTrace ct = counterTrace(phaseT(), phase(Q.and(R.negate())), phase(R.negate()),
					phase(S.and(R.negate()).and(T.negate())), phase(R.negate()), phase(T.and(R.negate())),
					phase(P.negate().and(R.negate())), phase(R), phaseT());
			return ct;
		}
		throw new PatternScopeNotImplemented(scope.getClass(), getClass());
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
