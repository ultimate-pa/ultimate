package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.guardedupdate;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGroupKey;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.KeyedInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.TranslatedInterferenceOfEdge;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class GuardedUpdateInterference extends KeyedInterferenceSet<GuardedUpdateInterference.GuardedUpdateGroup> {

	public record GuardedUpdateGroup(Map<TranslatedInterferenceOfEdge, GuardedUpdate> updatesByEdge) {
		public GuardedUpdateGroup {
			updatesByEdge = Collections.unmodifiableMap(new LinkedHashMap<>(updatesByEdge));
		}

		public Collection<GuardedUpdate> updates() {
			return updatesByEdge.values();
		}
	}

	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final IPredicate mFalsePredicate;

	public GuardedUpdateInterference(final Map<InterferenceGroupKey, GuardedUpdateGroup> summaryByKey,
			final Map<String, Set<IcfgLocation>> preForkSourcesByThread, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory) {
		super(summaryByKey, preForkSourcesByThread);
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mFalsePredicate = predicateFactory.newPredicate(managedScript.getScript().term("false"));
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final String observerThreadId,
			final Set<String> activeThreadIds, final Set<String> observerLockset, final IDomain domain,
			final int wideningThreshold,
			final SifaStats stats) {
		if (mSummaryByKey.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}
		final List<Entry<InterferenceGroupKey, GuardedUpdateGroup>> applicable =
				selectApplicableSummaries(observerThreadId, activeThreadIds, observerLockset, stats);
		if (applicable.isEmpty()) {
			return state;
		}
		IPredicate current = state;
		IPredicate frontier = state;
		for (int iteration = 1;; iteration++) {
			stats.increment(Key.INTERFERENCE_INNER_ITERATIONS);
			boolean hasGenerated = false;
			IPredicate generated = state;
			for (final Entry<InterferenceGroupKey, GuardedUpdateGroup> entry : applicable) {
				final IPredicate post = applyGroupToFrontier(frontier, entry.getValue(), domain);
				if (SmtUtils.isFalseLiteral(post.getFormula())) {
					continue;
				}
				if (!hasGenerated) {
					generated = post;
					hasGenerated = true;
				} else {
					generated = domain.join(generated, post);
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

	private IPredicate applyGroupToFrontier(final IPredicate frontier,
			final GuardedUpdateGroup groupedInterference, final IDomain domain) {
		boolean hasResult = false;
		IPredicate result = mFalsePredicate;
		for (final GuardedUpdate update : groupedInterference.updates()) {
			final IPredicate post = applyUpdate(frontier, update);
			if (SmtUtils.isFalseLiteral(post.getFormula())) {
				continue;
			}
			if (!hasResult) {
				result = post;
				hasResult = true;
			} else {
				result = domain.join(result, post);
			}
		}
		return hasResult ? result : mFalsePredicate;
	}

	@Override
	protected GuardedUpdateGroup widenSummaries(final GuardedUpdateGroup left, final GuardedUpdateGroup right,
			final IDomain domain) {
		final LinkedHashMap<TranslatedInterferenceOfEdge, GuardedUpdate> widened =
				new LinkedHashMap<>(left.updatesByEdge());
		right.updatesByEdge().forEach((edge, rightUpdate) -> widened.merge(edge, rightUpdate,
				(leftUpdate, ignored) -> widen(leftUpdate, rightUpdate, domain)));
		return new GuardedUpdateGroup(widened);
	}

	@Override
	protected boolean isTrivialSummary(final GuardedUpdateGroup group) {
		return group.updates().stream().allMatch(GuardedUpdate::hasFalseEffect);
	}

	@Override
	protected boolean summaryIsSubsumedBy(final GuardedUpdateGroup left, final GuardedUpdateGroup right,
			final IDomain domain) {
		for (final Entry<TranslatedInterferenceOfEdge, GuardedUpdate> entry : left.updatesByEdge().entrySet()) {
			final GuardedUpdate rightUpdate = right.updatesByEdge().get(entry.getKey());
			if (rightUpdate == null || !isSubsumed(entry.getValue(), rightUpdate, domain)) {
				return false;
			}
		}
		return true;
	}

	@Override
	protected KeyedInterferenceSet<GuardedUpdateGroup> withSummaries(
			final Map<InterferenceGroupKey, GuardedUpdateGroup> summaries) {
		return new GuardedUpdateInterference(summaries, mPreForkSourcesByThread, mManagedScript, mPredicateFactory);
	}

	private static boolean isSubsumed(final GuardedUpdate left, final GuardedUpdate right, final IDomain domain) {
		if (!domain.isSubsetEq(left.effect(), right.effect()).isTrueForAbstraction()
				|| left.hasGuard() != right.hasGuard()) {
			return false;
		}
		return !left.hasGuard() || domain.isSubsetEq(left.guard(), right.guard()).isTrueForAbstraction();
	}

	private static GuardedUpdate widen(final GuardedUpdate left, final GuardedUpdate right, final IDomain domain) {
		return new GuardedUpdate(widenGuards(left, right, domain), widenEffects(left, right, domain),
				mergeModifiedGlobals(left, right));
	}

	private static IPredicate widenGuards(final GuardedUpdate left, final GuardedUpdate right, final IDomain domain) {
		if (!left.hasGuard() || !right.hasGuard()) {
			return null;
		}
		if (SmtUtils.isFalseLiteral(left.guard().getFormula())) {
			return right.guard();
		}
		if (SmtUtils.isFalseLiteral(right.guard().getFormula())) {
			return left.guard();
		}
		return domain.widen(left.guard(), right.guard());
	}

	private static IPredicate widenEffects(final GuardedUpdate left, final GuardedUpdate right, final IDomain domain) {
		if (left.hasFalseEffect()) {
			return right.effect();
		}
		if (right.hasFalseEffect()) {
			return left.effect();
		}
		return domain.widen(left.effect(), right.effect());
	}

	private IPredicate applyUpdate(final IPredicate state, final GuardedUpdate update) {
		if (update.hasFalseEffect()) {
			return mFalsePredicate;
		}

		final Script script = mManagedScript.getScript();
		final ArrayList<Term> results = new ArrayList<>();
		for (final Term stateDisjunct : SmtUtils.getDisjuncts(state.getFormula())) {
			if (!update.hasGuard()) {
				addOverwriteResult(results, stateDisjunct, null, update, script);
				continue;
			}
			for (final Term guardDisjunct : update.guardDisjuncts()) {
				addOverwriteResult(results, stateDisjunct, guardDisjunct, update, script);
			}
		}
		if (results.isEmpty()) {
			return mFalsePredicate;
		}
		return mPredicateFactory.newPredicate(results.size() == 1 ? results.get(0) : SmtUtils.or(script, results));
	}

	private static void addOverwriteResult(final ArrayList<Term> results, final Term state, final Term guard,
			final GuardedUpdate update, final Script script) {
		final Term guardedState = guard == null ? state
				: SmtUtils.andWithExtendedLocalSimplification(script, state, guard);
		if (SmtUtils.isFalseLiteral(guardedState)
				|| SmtUtils.checkSatTerm(script, guardedState) == Script.LBool.UNSAT) {
			return;
		}
		final Term projected = update.modifiedGlobals().isEmpty() ? guardedState
				: forgetChangedConjuncts(guardedState, update.modifiedGlobals(), script);
		results.add(SmtUtils.and(script, projected, update.effect().getFormula()));
	}

	private static Term forgetChangedConjuncts(final Term formula, final Set<TermVariable> changedVars,
			final Script script) {
		final Term[] conjuncts = SmtUtils.getConjuncts(formula);
		final Term[] kept = Stream.of(conjuncts)
				.filter(conjunct -> Stream.of(conjunct.getFreeVars()).noneMatch(changedVars::contains))
				.toArray(Term[]::new);
		return kept.length == conjuncts.length ? formula
				: kept.length == 0 ? script.term("true")
						: kept.length == 1 ? kept[0] : SmtUtils.and(script, kept);
	}

	private static Set<TermVariable> mergeModifiedGlobals(final GuardedUpdate left, final GuardedUpdate right) {
		return Stream.concat(left.modifiedGlobals().stream(), right.modifiedGlobals().stream())
				.collect(Collectors.toUnmodifiableSet());
	}
}
