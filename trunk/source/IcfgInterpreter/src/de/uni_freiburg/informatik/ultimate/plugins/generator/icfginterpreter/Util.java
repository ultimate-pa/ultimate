package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class Util {
	public static List<ApplicationTerm> extractSelects(final Term term) {
		final List<ApplicationTerm> out = new ArrayList<>();
		final ArrayDeque<Term> terms = new ArrayDeque<>();
		terms.add(term);

		while (!terms.isEmpty()) {
			final Term subTerm = terms.pop();
			if (subTerm instanceof final ApplicationTerm at) {
				if (at.getFunction().getName().equals(SMTLIBConstants.SELECT)) {
					out.add(at);
				} else {
					terms.addAll(List.of(at.getParameters()));
				}
			}
		}

		return out;
	}

	public static Pair<TermVariable, List<Term>> selectToKeyPair(final ApplicationTerm select) {
		final ArrayDeque<Term> keys = new ArrayDeque<>();
		Term arrayTerm = null;

		ApplicationTerm current = select;
		while (current.getFunction().getName().equals(SMTLIBConstants.SELECT)) {
			keys.push(current.getParameters()[1]);

			final Term subTerm = current.getParameters()[0];
			if (subTerm instanceof final ApplicationTerm at) {
				current = at;
			} else {
				arrayTerm = subTerm;
				break;
			}
		}
		return new Pair<>((TermVariable) arrayTerm, List.of(keys.toArray(new Term[keys.size()])));
	}
}
