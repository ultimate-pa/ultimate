package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CongruenceClosure;

public class CongruenceClosureSmtUtils {
	public static <NODE extends IEqNodeIdentifier<NODE>> Term congruenceClosureToTerm(final Script script,
			final CongruenceClosure<NODE> pa) {
		return SmtUtils.and(script, congruenceClosureToCube(script, pa));
	}

	public static <NODE extends IEqNodeIdentifier<NODE>> List<Term> congruenceClosureToCube(final Script script,
//	public static <NODE extends ICongruenceClosureElement<NODE>> List<Term> congruenceClosureToCube(final Script script,
			final CongruenceClosure<NODE> pa) {
		if (pa.isInconsistent()) {
			return Collections.emptyList();
		}

		final List<Term> elementEqualities = pa.getSupportingElementEqualities().entrySet().stream()
				.map(en -> script.term("=", en.getKey().getTerm(), en.getValue().getTerm()))
				.collect(Collectors.toList());
		final List<Term> elementDisequalities = pa.getElementDisequalities().entrySet().stream()
				.map(pair -> script.term("distinct", pair.getKey().getTerm(), pair.getValue().getTerm()))
				.collect(Collectors.toList());

		final List<Term> result = new ArrayList<>(elementEqualities.size() + elementDisequalities.size());
		result.addAll(elementEqualities);
		result.addAll(elementDisequalities);
		return result;
	}

}
