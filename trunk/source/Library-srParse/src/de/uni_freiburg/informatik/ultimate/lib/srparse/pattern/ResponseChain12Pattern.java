package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;

/**
 * {scope}, it is always the case that if "P" holds, then "S" eventually holds and is succeeded by "T".
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ResponseChain12Pattern extends PatternType {
	public ResponseChain12Pattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public CounterTrace transform(final CDD[] cdds, final int[] durations) {
		assert cdds.length == 3;

		final SrParseScope scope = getScope();
		final CDD P = cdds[2];
		final CDD S = cdds[1];
		final CDD T = cdds[0];

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
		sb.append(getCdds().get(2).toBoogieString());
		sb.append("\" holds, then \"");
		sb.append(getCdds().get(1).toBoogieString());
		sb.append("\" eventually holds and is succeeded by \"");
		sb.append(getCdds().get(0).toBoogieString());
		sb.append("\"");
		return sb.toString();
	}

	@Override
	public PatternType rename(final String newName) {
		return new ResponseChain12Pattern(getScope(), newName, getCdds(), getDuration());
	}
}
