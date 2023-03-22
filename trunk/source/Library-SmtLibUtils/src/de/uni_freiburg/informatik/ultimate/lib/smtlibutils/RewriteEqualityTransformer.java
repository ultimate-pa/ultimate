package de.uni_freiburg.informatik.ultimate.lib.smtlibutils;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/**
 * Replaces equalities (atoms of the form a = b) with (a ≤ b /\ a ≥ b) and inequalities (a != b) with (a > b \/ a < b).
 *
 * @author Jan Leike
 */
public class RewriteEqualityTransformer extends TermTransformer {
	private static final Set<String> SUPPORTED_SORTS =
			new HashSet<>(Arrays.asList(new String[] { SmtSortUtils.INT_SORT, SmtSortUtils.REAL_SORT }));
	private final Script mScript;

	public RewriteEqualityTransformer(final Script script) {
		assert script != null;
		mScript = script;
	}

	@Override
	protected void convert(final Term term) {
		if (!(term instanceof ApplicationTerm)) {
			super.convert(term);
			return;
		}
		final ApplicationTerm appt = (ApplicationTerm) term;
		final String funName = appt.getFunction().getName();
		if (!"=".equals(funName) && !"distinct".equals(funName)) {
			super.convert(term);
			return;
		}
		final String paramSortName = appt.getParameters()[0].getSort().getName();

		if (!SUPPORTED_SORTS.contains(paramSortName)) {
			setResult(term);
			return;
		}

		if ("=".equals(funName)) {
			assert appt.getParameters().length == 2 : "equality with more than two parameters not yet supported";
			final Term param1 = mScript.term("<=", appt.getParameters());
			final Term param2 = mScript.term(">=", appt.getParameters());
			setResult(mScript.term("and", param1, param2));
			return;
		} else if ("distinct".equals(funName)) {
			assert appt.getParameters().length == 2 : "distinct with more than two parameters not yet supported";
			final Term param1 = mScript.term("<", appt.getParameters());
			final Term param2 = mScript.term(">", appt.getParameters());
			setResult(mScript.term("or", param1, param2));
			return;
		}

	}
}