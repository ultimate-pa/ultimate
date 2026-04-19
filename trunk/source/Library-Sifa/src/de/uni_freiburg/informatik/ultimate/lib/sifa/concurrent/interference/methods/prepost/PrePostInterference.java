package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.prepost;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
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
		final Map<AbstractLocationPair, PrePostPair> widened = new LinkedHashMap<>();
		for (final Entry<AbstractLocationPair, PrePostPair> entry : mInterferenceByAbstractLocationPair.entrySet()) {
			final PrePostPair otherGroup = typedOther.mInterferenceByAbstractLocationPair.get(entry.getKey());
			final PrePostPair widenedGroup = otherGroup == null ? entry.getValue()
					: new PrePostPair(domain.widen(entry.getValue().preState(), otherGroup.preState()),
							domain.widen(entry.getValue().postState(), otherGroup.postState()));
			if (!isTrivialPair(widenedGroup)) {
				widened.put(entry.getKey(), widenedGroup);
			}
		}
		for (final Entry<AbstractLocationPair, PrePostPair> entry : typedOther.mInterferenceByAbstractLocationPair.entrySet()) {
			if (!widened.containsKey(entry.getKey()) && !isTrivialPair(entry.getValue())) {
				widened.put(entry.getKey(), entry.getValue());
			}
		}
		return widened.isEmpty() ? null : new PrePostInterference(widened, mManagedScript);
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PrePostInterference typedOther)) {
			return false;
		}
		for (final Entry<AbstractLocationPair, PrePostPair> entry : mInterferenceByAbstractLocationPair.entrySet()) {
			final PrePostPair otherGroup = typedOther.mInterferenceByAbstractLocationPair.get(entry.getKey());
			if (otherGroup == null
					|| !domain.isSubsetEq(entry.getValue().preState(), otherGroup.preState()).isTrueForAbstraction()
					|| !domain.isSubsetEq(entry.getValue().postState(), otherGroup.postState()).isTrueForAbstraction()) {
				return false;
			}
		}
		return true;
	}

	private boolean intersects(final IPredicate state, final IPredicate preState) {
		final Script script = mManagedScript.getScript();
		final Term guardedState =
				SmtUtils.andWithExtendedLocalSimplification(script, state.getFormula(), preState.getFormula());
		return !SmtUtils.isFalseLiteral(guardedState) && SmtUtils.checkSatTerm(script, guardedState) != Script.LBool.UNSAT;
	}

	private static boolean isTrivialPair(final PrePostPair pair) {
		return SmtUtils.isFalseLiteral(pair.preState().getFormula())
				|| SmtUtils.isFalseLiteral(pair.postState().getFormula());
	}
}
