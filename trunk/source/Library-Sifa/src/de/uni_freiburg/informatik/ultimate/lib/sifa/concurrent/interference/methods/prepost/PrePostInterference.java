package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.prepost;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceMethodHelpers;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class PrePostInterference implements IInterference {

	public record PrePostPair(IPredicate preState, IPredicate postState) {
	}

	private final Map<AbstractLocationPair, PrePostPair> mInterferenceByAbstractLocationPair;
	private final ManagedScript mManagedScript;

	public PrePostInterference(final Map<AbstractLocationPair, PrePostPair> interferenceByAbstractLocationPair,
			final ManagedScript managedScript) {
		mInterferenceByAbstractLocationPair = Map.copyOf(interferenceByAbstractLocationPair);
		mManagedScript = managedScript;
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final IDomain domain, final int wideningThreshold,
			final SifaStats stats) {
		if (mInterferenceByAbstractLocationPair.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}

		IPredicate current = state;
		IPredicate frontier = state;
		final ArrayList<PrePostPair> remaining = new ArrayList<>(mInterferenceByAbstractLocationPair.values());
		for (int iteration = 1;; iteration++) {
			stats.increment(Key.INTERFERENCE_INNER_ITERATIONS);
			boolean hasGenerated = false;
			IPredicate generated = state;
			for (final Iterator<PrePostPair> iterator = remaining.iterator(); iterator.hasNext();) {
				final PrePostPair pair = iterator.next();
				if (!intersects(frontier, pair.preState())) {
					continue;
				}
				iterator.remove();
				if (SmtUtils.isFalseLiteral(pair.postState().getFormula())) {
					continue;
				}
				if (!hasGenerated) {
					generated = pair.postState();
					hasGenerated = true;
				} else {
					generated = domain.join(generated, pair.postState());
				}
			}
			if (!hasGenerated || domain.isSubsetEq(generated, current).isTrueForAbstraction()) {
				return current;
			}

			final IPredicate expanded = domain.join(current, generated);
			final IPredicate next;
			if (iteration > wideningThreshold) {
				next = domain.widen(current, expanded);
				stats.increment(Key.INTERFERENCE_INNER_WIDENINGS);
			} else {
				next = expanded;
			}
			if (domain.isSubsetEq(next, current).isTrueForAbstraction()) {
				return current;
			}
			current = next;
			frontier = generated;
		}
	}

	@Override
	public IInterference widen(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PrePostInterference typedOther)) {
			throw new IllegalArgumentException("Cannot widen PrePostInterference with " + other.getClass().getSimpleName());
		}
		return new PrePostInterference(
				InterferenceMethodHelpers.widen(mInterferenceByAbstractLocationPair,
						typedOther.mInterferenceByAbstractLocationPair,
						(left, right) -> new PrePostPair(domain.widen(left.preState(), right.preState()),
								domain.widen(left.postState(), right.postState()))),
				mManagedScript);
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		return other instanceof PrePostInterference typedOther
				&& InterferenceMethodHelpers.isSubsumed(mInterferenceByAbstractLocationPair,
						typedOther.mInterferenceByAbstractLocationPair,
						(left, right) -> domain.isSubsetEq(left.preState(), right.preState()).isTrueForAbstraction()
								&& domain.isSubsetEq(left.postState(), right.postState()).isTrueForAbstraction());
	}

	@Override
	public boolean isTrivial() {
		return mInterferenceByAbstractLocationPair.isEmpty()
				|| mInterferenceByAbstractLocationPair.values().stream()
						.allMatch(pair -> SmtUtils.isFalseLiteral(pair.preState().getFormula())
								|| SmtUtils.isFalseLiteral(pair.postState().getFormula()));
	}

	@Override
	public int size() {
		return mInterferenceByAbstractLocationPair.size();
	}

	private boolean intersects(final IPredicate state, final IPredicate preState) {
		final Script script = mManagedScript.getScript();
		final Term guardedState =
				SmtUtils.andWithExtendedLocalSimplification(script, state.getFormula(), preState.getFormula());
		return !SmtUtils.isFalseLiteral(guardedState) && SmtUtils.checkSatTerm(script, guardedState) != Script.LBool.UNSAT;
	}
}
