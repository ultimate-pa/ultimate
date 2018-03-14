package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PatternToPEA;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;

public class UniversalityPattern extends PatternType {

	public UniversalityPattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public PhaseEventAutomata transform(final PatternToPEA peaTrans, final Map<String, Integer> id2bounds) {
		/*
		 * CDD p_cdd = BooleanDecision.create("ANB_Request_valid = 1"); CDD q_cdd = BooleanDecision.create(
		 * "ANB_Teilbremsung_Freigabe = 1").and( BooleanDecision.create("ANB_info_Teilbremsung = 1") ); CDD r_cdd =
		 * p_cdd;
		 */

		final CDD p_cdd = getCdds().get(0);
		final CDD q_cdd = getScope().getCdd1();
		final CDD r_cdd = getScope().getCdd2();

		return peaTrans.universalityPattern(getId(), p_cdd, q_cdd, r_cdd, getScope().toString());
	}

	@Override
	public String toString() {
		return "it is always the case that \"" + getCdds().get(0) + "\" holds";
	}
}
