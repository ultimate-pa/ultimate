package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PatternToPEA;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;

public class BndPossResponsePattern extends PatternType {

	public BndPossResponsePattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public PhaseEventAutomata transform(final PatternToPEA peaTrans, final Map<String, Integer> id2bounds) {
		throw new UnsupportedOperationException();
	}

	@Override
	public String toString() {
		return "if \"" + getCdds().get(1) + "\" holds, then there is at least one execution sequence such that \""
				+ getCdds().get(0) + "\" holds after at most \"" + getDuration().get(0) + "\" time units";
	}

	@Override
	public PatternType rename(final String newName) {
		return new BndPossResponsePattern(getScope(), newName, getCdds(), getDuration());
	}
}
