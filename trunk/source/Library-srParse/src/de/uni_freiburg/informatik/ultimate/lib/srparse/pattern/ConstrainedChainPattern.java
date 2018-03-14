package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PatternToPEA;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;

public class ConstrainedChainPattern extends PatternType {

	public ConstrainedChainPattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public PhaseEventAutomata transform(final PatternToPEA peaTrans, final Map<String, Integer> id2bounds) {
		throw new UnsupportedOperationException();
	}

	@Override
	public String toString() {
		return "it is always the case that if \"" + getCdds().get(5) + "\" holds, then \"" + getCdds().get(4)
				+ "\" eventually holds and is succeeded by \"" + getCdds().get(3) + "\", where \"" + getCdds().get(2)
				+ "\" does not hold between \"" + getCdds().get(1) + "\" and \"" + getCdds().get(0) + "\"";
	}
}
