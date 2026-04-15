package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceFixpointUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceMethodHelpers;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition.PreparedRelation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public final class StrongestPostconditionInterference implements IInterference {

	public record RelationalInterference(IPredicate relationalInterference,
			PreparedRelation preparedRelationalInterference) {
	}

	private final Map<AbstractLocationPair, RelationalInterference> mInterferenceByAbstractLocationPair;
	private final RelationalPredicatePostcondition mPostcondition;

	public StrongestPostconditionInterference(
			final Map<AbstractLocationPair, RelationalInterference> interferenceByAbstractLocationPair,
			final RelationalPredicatePostcondition postcondition) {
		mInterferenceByAbstractLocationPair = Map.copyOf(interferenceByAbstractLocationPair);
		mPostcondition = postcondition;
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final IDomain domain, final int wideningThreshold,
			final SifaStats stats) {
		return InterferenceFixpointUtils.applyUntilFixpoint(state, mInterferenceByAbstractLocationPair.values(),
				this::applyGroupToFrontier,
				domain, wideningThreshold, stats);
	}

	private IPredicate applyGroupToFrontier(final IPredicate frontier, final RelationalInterference relationalInterference) {
		return mPostcondition.strongestPostcondition(frontier,
				relationalInterference.preparedRelationalInterference());
	}

	@Override
	public IInterference widen(final IInterference other, final IDomain domain) {
		if (!(other instanceof final StrongestPostconditionInterference typedOther)) {
			throw new IllegalArgumentException(
					"Cannot widen StrongestPostconditionInterference with " + other.getClass().getSimpleName());
		}
		return new StrongestPostconditionInterference(
				InterferenceMethodHelpers.widen(mInterferenceByAbstractLocationPair,
						typedOther.mInterferenceByAbstractLocationPair, (left, right) -> {
							final IPredicate widenedRelationalInterference =
									domain.widen(left.relationalInterference(), right.relationalInterference());
							return new RelationalInterference(widenedRelationalInterference,
									mPostcondition.prepareRelation(widenedRelationalInterference));
						}),
				mPostcondition);
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		return other instanceof StrongestPostconditionInterference typedOther
				&& InterferenceMethodHelpers.isSubsumed(mInterferenceByAbstractLocationPair,
						typedOther.mInterferenceByAbstractLocationPair,
						(left, right) -> domain.isSubsetEq(left.relationalInterference(), right.relationalInterference())
								.isTrueForAbstraction());
	}

	@Override
	public boolean isTrivial() {
		return mInterferenceByAbstractLocationPair.isEmpty()
				|| mInterferenceByAbstractLocationPair.values().stream().allMatch(
						interference -> SmtUtils.isFalseLiteral(interference.relationalInterference().getFormula()));
	}

	@Override
	public int size() {
		return mInterferenceByAbstractLocationPair.size();
	}
}
