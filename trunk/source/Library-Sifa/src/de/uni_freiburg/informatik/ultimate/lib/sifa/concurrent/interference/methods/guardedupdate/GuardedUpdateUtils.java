package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.guardedupdate;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class GuardedUpdateUtils {

	private GuardedUpdateUtils() {
	}

	public static IPredicate extractTransitionAwareGuard(final IPredicate fullRelation, final Set<? extends Term> primedVars,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory) {
		final Term[] conjuncts = SmtUtils.getConjuncts(fullRelation.getFormula());
		final List<Term> preOnly = new ArrayList<>();
		for (final Term conjunct : conjuncts) {
			boolean hasPrimed = false;
			for (final TermVariable freeVar : conjunct.getFreeVars()) {
				if (primedVars.contains(freeVar)) {
					hasPrimed = true;
					break;
				}
			}
			if (!hasPrimed) {
				preOnly.add(conjunct);
			}
		}
		if (preOnly.isEmpty()) {
			return null;
		}
		return predicateFactory.newPredicate(SmtUtils.and(managedScript.getScript(), preOnly));
	}

}
