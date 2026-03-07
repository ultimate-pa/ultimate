package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public class PerThreadInterference implements IInterference {

	private final IPredicate mPredicate;

	public PerThreadInterference(final IPredicate predicate) {
		mPredicate = predicate;
	}

	@Override
	public Collection<IPredicate> getPredicates() {
		return List.of(mPredicate);
	}

	@Override
	public boolean isTrivial() {
		return SmtUtils.isFalseLiteral(mPredicate.getFormula());
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PerThreadInterference otherFlat)) {
			return false;
		}
		return domain.isSubsetEq(mPredicate, otherFlat.mPredicate).isTrueForAbstraction();
	}

	@Override
	public IInterference widen(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PerThreadInterference otherFlat)) {
			throw new IllegalArgumentException(
					"Cannot widen PerThreadInterference with " + other.getClass().getSimpleName());
		}
		return new PerThreadInterference(domain.widen(mPredicate, otherFlat.mPredicate));
	}

	@Override
	public int size() {
		return 1;
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final IDomain domain,
			final RelationalPredicatePostcondition postcondition, final GhostVariableManager ghostVars,
			final ManagedScript managedScript, final BasicPredicateFactory factory, final int wideningThreshold,
			final SifaStats stats) {
		// opt: trivial (false predicate)
		if (isTrivial()) {
			return state;
		}
		return InterferenceUtils.applyUntilFixpoint(state,
				InterferenceUtils.prepareNonFalseRelations(List.of(mPredicate), postcondition), domain, postcondition,
				wideningThreshold, stats);
	}
}
