package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.srParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.srParseScopeAfterUntil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.srParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.srParseScopeBetween;
import de.uni_freiburg.informatik.ultimate.lib.srparse.srParseScopeGlob;

public class InstAbsPattern extends PatternType {
	// erwartet cdds rückwärts
	@Override
	public void transform() {

		// Case: GLOBALLY
		if (scope instanceof srParseScopeGlob) {
			if (cdds.size() != 1) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}

			final CDD p_cdd = cdds.get(0); // für Duration Calculus muß das als CDD gegeben sein
			final CDD q_cdd = getDefaultQ_cdd();
			final CDD r_cdd = getDefaultR_cdd();

			pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
		}
		// CASE: BEFORE R
		else if (scope instanceof srParseScopeBefore) {
			if (cdds.size() != 2) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}

			final CDD p_cdd = cdds.get(0); // für Duration Calculus muß das als CDD gegeben sein
			final CDD q_cdd = getDefaultQ_cdd();
			final CDD r_cdd = cdds.get(1);

			pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope.toString());

		}
		// CASE: AFTER Q UNTIL R
		else if (scope instanceof srParseScopeAfterUntil) {
			if (cdds.size() != 1) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}

			final CDD p_cdd = cdds.get(0);
			final CDD q_cdd = scope.getCdd1();
			final CDD r_cdd = scope.getCdd2();

			pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope.toString());

		}
		// CASE: AFTER Q
		else if (scope instanceof srParseScopeAfter) {
			if (cdds.size() != 1) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}
			final CDD p_cdd = cdds.get(0); // für Duration Calculus muß das als CDD gegeben sein
			final CDD q_cdd = scope.getCdd1();
			final CDD r_cdd = getDefaultR_cdd();

			pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
		}
		// CASE: BETWEEN Q AND R
		else if (scope instanceof srParseScopeBetween) {
			if (cdds.size() != 1) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}

			final CDD p_cdd = cdds.get(0); // für Duration Calculus muß das als CDD gegeben sein
			final CDD q_cdd = scope.getCdd1();
			final CDD r_cdd = scope.getCdd2();

			pea = peaTransformator.absencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
			// return this.getFormulaInLTL();
		}
	}

	@Override
	public String toString() {
		String res = new String();

		res = "it is never the case that \"" + cdds.get(0) + "\" holds";

		return res;
	}
}
