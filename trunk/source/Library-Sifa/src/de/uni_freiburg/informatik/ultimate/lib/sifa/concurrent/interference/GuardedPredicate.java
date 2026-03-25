package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Guarded interference effect: guard (pre-condition, nullable), effect (post-values),
 * and optionally the set of modified globals (for SYNTACTIC/SYNTACTIC_PRECISE).
 */
public record GuardedPredicate(IPredicate guard, IPredicate effect, Set<TermVariable> modifiedGlobals) {

	public static GuardedPredicate unguarded(final IPredicate effect) {
		return new GuardedPredicate(null, effect, null);
	}

	public GuardedPredicate(final IPredicate guard, final IPredicate effect) {
		this(guard, effect, null);
	}

	public boolean hasGuard() {
		return guard != null;
	}

	public boolean hasModifiedGlobals() {
		return modifiedGlobals != null;
	}
}
