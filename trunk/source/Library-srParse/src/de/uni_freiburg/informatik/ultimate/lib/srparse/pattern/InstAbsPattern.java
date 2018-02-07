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
		if (mScope instanceof srParseScopeGlob) {
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
		else if (mScope instanceof srParseScopeBefore) {
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
		else if (mScope instanceof srParseScopeAfterUntil) {
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
		else if (mScope instanceof srParseScopeAfter) {
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
		else if (mScope instanceof srParseScopeBetween) {
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
