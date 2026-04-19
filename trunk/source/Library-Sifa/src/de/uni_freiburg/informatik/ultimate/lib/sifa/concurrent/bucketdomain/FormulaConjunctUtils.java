package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class FormulaConjunctUtils {

	private FormulaConjunctUtils() {
	}

	public static void collectConjuncts(final Term formula, final List<Term> result) {
		final Term[] conjuncts = SmtUtils.getConjuncts(formula);
		if (conjuncts.length == 1 && conjuncts[0] == formula) {
			result.add(formula);
			return;
		}
		for (final Term conjunct : conjuncts) {
			collectConjuncts(conjunct, result);
		}
	}
}
