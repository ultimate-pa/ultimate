package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.guardedupdate;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public record GuardedUpdate(IPredicate guard, IPredicate effect, Set<TermVariable> modifiedGlobals,
		List<Term> guardDisjuncts, boolean hasFalseEffect, boolean requiresArrayFallback) {

	public GuardedUpdate(final IPredicate guard, final IPredicate effect, final Set<TermVariable> modifiedGlobals) {
		this(guard, effect, modifiedGlobals, guard == null ? List.of() : List.of(SmtUtils.getDisjuncts(guard.getFormula())),
				SmtUtils.isFalseLiteral(effect.getFormula()),
				InterferenceUtils.containsArraySortedVar(modifiedGlobals == null ? Set.of() : modifiedGlobals)
						|| InterferenceUtils.referencesArraySortedTerm(effect.getFormula())
						|| (guard != null && InterferenceUtils.referencesArraySortedTerm(guard.getFormula())));
	}

	public GuardedUpdate {
		modifiedGlobals = modifiedGlobals == null ? Set.of() : Set.copyOf(modifiedGlobals);
		guardDisjuncts = guardDisjuncts == null ? List.of() : List.copyOf(guardDisjuncts);
	}

	public boolean hasGuard() {
		return guard != null;
	}
}
