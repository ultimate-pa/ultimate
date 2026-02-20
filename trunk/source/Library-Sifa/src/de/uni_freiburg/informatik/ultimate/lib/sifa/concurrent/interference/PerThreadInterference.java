package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.InterferenceMergeMode;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public class PerThreadInterference implements IInterference {

	private final IPredicate mPredicate;
	private final InterferenceMergeMode mMergeMode;

	public PerThreadInterference(final IPredicate predicate, final InterferenceMergeMode mergeMode) {
		mPredicate = predicate;
		mMergeMode = mergeMode;
	}

	@Override
	public IInterference build(final String threadId, final Map<IcfgLocation, IPredicate> locationStates,
			final InterferenceFactory factory) {
		IPredicate merged = null;
		for (final EdgePredicate edgePred : factory.collectEdgePredicates(threadId, locationStates)) {
			merged = merged == null ? edgePred.predicate() : factory.merge(merged, edgePred.predicate());
		}
		if (merged == null) {
			merged = factory.falsePredicate();
		}
		return new PerThreadInterference(merged, factory.getMergeMode());
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
		if (mMergeMode != otherFlat.mMergeMode) {
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
		if (mMergeMode != otherFlat.mMergeMode) {
			throw new IllegalArgumentException("Cannot widen PerThreadInterference with different merge modes");
		}
		return new PerThreadInterference(domain.widen(mPredicate, otherFlat.mPredicate), mMergeMode);
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
		if (isTrivial()) {
			return state;
		}
		return InterferenceUtils.applyUntilFixpoint(state,
				InterferenceUtils.prepareNonFalseRelations(List.of(mPredicate), postcondition), mMergeMode, domain,
				postcondition, managedScript, factory, wideningThreshold, stats);
	}
}
