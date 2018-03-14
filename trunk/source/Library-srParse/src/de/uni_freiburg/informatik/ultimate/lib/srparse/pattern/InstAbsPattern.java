package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfterUntil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBetween;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlob;

public class InstAbsPattern extends PatternType {
	// erwartet cdds rückwärts
	@Override
	public void transform(Map<String, Integer> id2bounds) {

		// Case: GLOBALLY
		if (mScope instanceof SrParseScopeGlob) {
			if (mCdds.size() != 1) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}

			final CDD p_cdd = mCdds.get(0); // für Duration Calculus muß das als CDD gegeben sein
			final CDD q_cdd = DEFAULT_Q;
			final CDD r_cdd = DEFAULT_R;

			mPea = mPeaTransformator.absencePattern(mId, p_cdd, q_cdd, r_cdd, mScope.toString());
		}
		// CASE: BEFORE R
		else if (mScope instanceof SrParseScopeBefore) {
			if (mCdds.size() != 2) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}

			final CDD p_cdd = mCdds.get(0); // für Duration Calculus muß das als CDD gegeben sein
			final CDD q_cdd = DEFAULT_Q;
			final CDD r_cdd = mCdds.get(1);

			mPea = mPeaTransformator.absencePattern(mId, p_cdd, q_cdd, r_cdd, mScope.toString());

		}
		// CASE: AFTER Q UNTIL R
		else if (mScope instanceof SrParseScopeAfterUntil) {
			if (mCdds.size() != 1) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}

			final CDD p_cdd = mCdds.get(0);
			final CDD q_cdd = mScope.getCdd1();
			final CDD r_cdd = mScope.getCdd2();

			mPea = mPeaTransformator.absencePattern(mId, p_cdd, q_cdd, r_cdd, mScope.toString());

		}
		// CASE: AFTER Q
		else if (mScope instanceof SrParseScopeAfter) {
			if (mCdds.size() != 1) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}
			final CDD p_cdd = mCdds.get(0); // für Duration Calculus muß das als CDD gegeben sein
			final CDD q_cdd = mScope.getCdd1();
			final CDD r_cdd = DEFAULT_R;

			mPea = mPeaTransformator.absencePattern(mId, p_cdd, q_cdd, r_cdd, mScope.toString());
		}
		// CASE: BETWEEN Q AND R
		else if (mScope instanceof SrParseScopeBetween) {
			if (mCdds.size() != 1) {
				// Das AbsentPattern besitzt nur zwei-drei nonLiteralTerminals!
				System.out.println("ERROR: Wrong number of nonLiteralTerminals for the absentPattern");
			}

			final CDD p_cdd = mCdds.get(0); // für Duration Calculus muß das als CDD gegeben sein
			final CDD q_cdd = mScope.getCdd1();
			final CDD r_cdd = mScope.getCdd2();

			mPea = mPeaTransformator.absencePattern(mId, p_cdd, q_cdd, r_cdd, mScope.toString());
			// return this.getFormulaInLTL();
		}
	}

	@Override
	public String toString() {
		String res = new String();

		res = "it is never the case that \"" + mCdds.get(0) + "\" holds";

		return res;
	}
}
