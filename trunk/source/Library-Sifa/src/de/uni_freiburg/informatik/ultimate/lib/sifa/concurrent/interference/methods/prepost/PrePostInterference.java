package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.prepost;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGroupKey;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.KeyedInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain.ResultForAlteredInputs;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class PrePostInterference extends KeyedInterferenceSet<PrePostInterference.PrePostPair> {

	public record PrePostPair(IPredicate preState, IPredicate postState) {
	}

	private final ManagedScript mManagedScript;

	public PrePostInterference(final Map<InterferenceGroupKey, PrePostPair> summaryByKey,
			final Map<String, Set<IcfgLocation>> preForkSourcesByThread, final ManagedScript managedScript) {
		super(summaryByKey, preForkSourcesByThread);
		mManagedScript = managedScript;
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final String observerThreadId,
			final Set<String> activeThreadIds, final Set<String> observerLockset, final IDomain domain,
			final int wideningThreshold, final SifaStats stats) {
		if (mSummaryByKey.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}
		final List<Entry<InterferenceGroupKey, PrePostPair>> applicable =
				selectApplicableSummaries(observerThreadId, activeThreadIds, observerLockset, stats);
		if (applicable.isEmpty()) {
			return state;
		}
		IPredicate current = state;
		IPredicate frontier = state;
		final ArrayList<Entry<InterferenceGroupKey, PrePostPair>> remaining = new ArrayList<>(applicable);
		for (int iteration = 1;; iteration++) {
			stats.increment(Key.INTERFERENCE_INNER_ITERATIONS);
			boolean hasGenerated = false;
			IPredicate generated = state;
			for (final Iterator<Entry<InterferenceGroupKey, PrePostPair>> iterator = remaining.iterator();
					iterator.hasNext();) {
				final PrePostPair pair = iterator.next().getValue();
				if (!SmtUtils.isTrueLiteral(pair.preState().getFormula()) && !intersects(frontier, pair.preState())) {
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
			if (!hasGenerated) {
				return current;
			}
			final ResultForAlteredInputs genSubsetCur = domain.isSubsetEq(generated, current);
			generated = genSubsetCur.getLhs();
			current = genSubsetCur.getRhs();
			if (genSubsetCur.isTrueForAbstraction()) {
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
			final ResultForAlteredInputs nextSubsetCur = domain.isSubsetEq(next, current);
			current = nextSubsetCur.getRhs();
			if (nextSubsetCur.isTrueForAbstraction()) {
				return current;
			}
			current = nextSubsetCur.getLhs();
			frontier = generated;
		}
	}

	private boolean intersects(final IPredicate state, final IPredicate preState) {
		final Script script = mManagedScript.getScript();
		final Term guardedState =
				SmtUtils.andWithExtendedLocalSimplification(script, state.getFormula(), preState.getFormula());
		return !SmtUtils.isFalseLiteral(guardedState)
				&& SmtUtils.checkSatTerm(script, guardedState) != Script.LBool.UNSAT;
	}

	@Override
	protected PrePostPair widenSummaries(final PrePostPair left, final PrePostPair right, final IDomain domain) {
		return new PrePostPair(domain.widen(left.preState(), right.preState()),
				domain.widen(left.postState(), right.postState()));
	}

	@Override
	protected boolean isTrivialSummary(final PrePostPair summary) {
		return SmtUtils.isFalseLiteral(summary.preState().getFormula())
				|| SmtUtils.isFalseLiteral(summary.postState().getFormula());
	}

	@Override
	protected boolean summaryIsSubsumedBy(final PrePostPair left, final PrePostPair right, final IDomain domain) {
		return domain.isSubsetEq(left.preState(), right.preState()).isTrueForAbstraction()
				&& domain.isSubsetEq(left.postState(), right.postState()).isTrueForAbstraction();
	}

	@Override
	protected KeyedInterferenceSet<PrePostPair> withSummaries(final Map<InterferenceGroupKey, PrePostPair> summaries) {
		return new PrePostInterference(summaries, mPreForkSourcesByThread, mManagedScript);
	}
}
