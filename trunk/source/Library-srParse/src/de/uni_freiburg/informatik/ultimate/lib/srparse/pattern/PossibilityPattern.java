package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PatternToPEA;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;

public class PossibilityPattern extends PatternType {
	public PossibilityPattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public PhaseEventAutomata transform(final PatternToPEA peaTrans, final Map<String, Integer> id2bounds) {
		throw new PatternScopeNotImplemented(getScope().getClass(), getClass());
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
		sb.append("if \"");
		sb.append(getCdds().get(1).toBoogieString());
		sb.append("\" holds, then there is at least one execution sequence such that \"");
		sb.append(getCdds().get(0).toBoogieString());
		sb.append("\" eventually holds");
		return sb.toString();
	}

	@Override
	public PatternType rename(final String newName) {
		return new PossibilityPattern(getScope(), newName, getCdds(), getDuration());
	}
}
