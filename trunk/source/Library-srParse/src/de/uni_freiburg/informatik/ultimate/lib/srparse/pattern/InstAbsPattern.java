package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PatternToPEA;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfterUntil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBetween;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlob;


/*
 *  * {scope}, it is never the case that "S" holds.
 */
public class InstAbsPattern extends PatternType {
	public InstAbsPattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	// erwartet cdds rückwärts
	@Override
	public PhaseEventAutomata transform(final PatternToPEA peaTrans, final Map<String, Integer> id2bounds) {

		// Case: GLOBALLY
		if (getScope() instanceof SrParseScopeGlob) {
			if (getCdds().size() != 1) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}

			final CDD p_cdd = getCdds().get(0); // für Duration Calculus muß das als CDD gegeben sein
			final CDD q_cdd = DEFAULT_Q;
			final CDD r_cdd = DEFAULT_R;

			return peaTrans.absencePattern(getId(), p_cdd, q_cdd, r_cdd, getScope().toString());
		}
		// CASE: BEFORE R
		else if (getScope() instanceof SrParseScopeBefore) {
			if (getCdds().size() != 2) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}

			final CDD p_cdd = getCdds().get(0); // für Duration Calculus muß das als CDD gegeben sein
			final CDD q_cdd = DEFAULT_Q;
			final CDD r_cdd = getCdds().get(1);

			return peaTrans.absencePattern(getId(), p_cdd, q_cdd, r_cdd, getScope().toString());

		}
		// CASE: AFTER Q UNTIL R
		else if (getScope() instanceof SrParseScopeAfterUntil) {
			if (getCdds().size() != 1) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}

			final CDD p_cdd = getCdds().get(0);
			final CDD q_cdd = getScope().getCdd1();
			final CDD r_cdd = getScope().getCdd2();

			return peaTrans.absencePattern(getId(), p_cdd, q_cdd, r_cdd, getScope().toString());

		}
		// CASE: AFTER Q
		else if (getScope() instanceof SrParseScopeAfter) {
			if (getCdds().size() != 1) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}
			final CDD p_cdd = getCdds().get(0); // für Duration Calculus muß das als CDD gegeben sein
			final CDD q_cdd = getScope().getCdd1();
			final CDD r_cdd = DEFAULT_R;

			return peaTrans.absencePattern(getId(), p_cdd, q_cdd, r_cdd, getScope().toString());
		}
		// CASE: BETWEEN Q AND R
		else if (getScope() instanceof SrParseScopeBetween) {
			if (getCdds().size() != 1) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}

			final CDD p_cdd = getCdds().get(0); // für Duration Calculus muß das als CDD gegeben sein
			final CDD q_cdd = getScope().getCdd1();
			final CDD r_cdd = getScope().getCdd2();

			return peaTrans.absencePattern(getId(), p_cdd, q_cdd, r_cdd, getScope().toString());
			// return this.getFormulaInLTL();
		}
		throw new UnsupportedOperationException();
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
