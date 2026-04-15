package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.guardedupdate;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceFixpointUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceMethodHelpers;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class GuardedUpdateInterference implements IInterference {

	public record GuardedUpdateGroup(List<GuardedUpdate> updates) {
		public GuardedUpdateGroup {
			updates = List.copyOf(updates);
		}
	}

	private final Map<AbstractLocationPair, GuardedUpdateGroup> mInterferenceByAbstractLocationPair;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final IPredicate mFalsePredicate;

	public GuardedUpdateInterference(final Map<AbstractLocationPair, GuardedUpdateGroup> interferenceByAbstractLocationPair,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory) {
		mInterferenceByAbstractLocationPair = Map.copyOf(interferenceByAbstractLocationPair);
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mFalsePredicate = InterferenceMethodHelpers.falsePredicate(predicateFactory, managedScript);
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final IDomain domain, final int wideningThreshold,
			final SifaStats stats) {
		return InterferenceFixpointUtils.applyUntilFixpoint(state, mInterferenceByAbstractLocationPair.values(),
				(frontier, groupedInterference) -> applyGroupToFrontier(frontier, groupedInterference, domain),
				domain, wideningThreshold, stats);
	}

	private IPredicate applyGroupToFrontier(final IPredicate frontier, final GuardedUpdateGroup groupedInterference,
			final IDomain domain) {
		return InterferenceMethodHelpers.applyGroup(groupedInterference.updates(),
				update -> applyUpdate(frontier, update), domain, mFalsePredicate);
	}

	@Override
	public IInterference widen(final IInterference other, final IDomain domain) {
		if (!(other instanceof final GuardedUpdateInterference typedOther)) {
			throw new IllegalArgumentException(
					"Cannot widen GuardedUpdateInterference with " + other.getClass().getSimpleName());
		}
		return new GuardedUpdateInterference(
				InterferenceMethodHelpers.widen(mInterferenceByAbstractLocationPair,
						typedOther.mInterferenceByAbstractLocationPair,
						(left, right) -> widen(left, right, domain)),
				mManagedScript, mPredicateFactory);
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		return other instanceof GuardedUpdateInterference typedOther
				&& InterferenceMethodHelpers.isSubsumed(mInterferenceByAbstractLocationPair,
						typedOther.mInterferenceByAbstractLocationPair,
						(left, right) -> isSubsumed(left, right, domain));
	}

	@Override
	public boolean isTrivial() {
		return mInterferenceByAbstractLocationPair.isEmpty()
				|| mInterferenceByAbstractLocationPair.values().stream()
						.allMatch(group -> group.updates().stream().allMatch(GuardedUpdate::hasFalseEffect));
	}

	@Override
	public int size() {
		return mInterferenceByAbstractLocationPair.size();
	}

	private static boolean isSubsumed(final GuardedUpdateGroup left, final GuardedUpdateGroup right, final IDomain domain) {
		return left.updates().size() == right.updates().size()
				&& IntStream.range(0, left.updates().size())
						.allMatch(i -> isSubsumed(left.updates().get(i), right.updates().get(i), domain));
	}

	private static boolean isSubsumed(final GuardedUpdate left, final GuardedUpdate right, final IDomain domain) {
		if (!domain.isSubsetEq(left.effect(), right.effect()).isTrueForAbstraction() || left.hasGuard() != right.hasGuard()) {
			return false;
		}
		return !left.hasGuard() || domain.isSubsetEq(left.guard(), right.guard()).isTrueForAbstraction();
	}

	private static GuardedUpdateGroup widen(final GuardedUpdateGroup left, final GuardedUpdateGroup right,
			final IDomain domain) {
		final ArrayList<GuardedUpdate> widened = new ArrayList<>(Math.max(left.updates().size(), right.updates().size()));
		final int shared = Math.min(left.updates().size(), right.updates().size());
		for (int i = 0; i < shared; i++) {
			widened.add(widen(left.updates().get(i), right.updates().get(i), domain));
		}
		if (left.updates().size() > shared) {
			widened.addAll(left.updates().subList(shared, left.updates().size()));
		} else if (right.updates().size() > shared) {
			widened.addAll(right.updates().subList(shared, right.updates().size()));
		}
		return new GuardedUpdateGroup(widened);
	}

	private static GuardedUpdate widen(final GuardedUpdate left, final GuardedUpdate right, final IDomain domain) {
		return new GuardedUpdate(left.hasGuard() && right.hasGuard() ? domain.widen(left.guard(), right.guard()) : null,
				domain.widen(left.effect(), right.effect()), mergeModifiedGlobals(left, right));
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
		final Term guardedState = guard == null ? state : SmtUtils.andWithExtendedLocalSimplification(script, state, guard);
		if (SmtUtils.isFalseLiteral(guardedState) || SmtUtils.checkSatTerm(script, guardedState) == Script.LBool.UNSAT) {
			return;
		}
		final Term projected = update.modifiedGlobalsOrEmpty().isEmpty() ? guardedState
				: forgetChangedConjuncts(guardedState, update.modifiedGlobalsOrEmpty(), script);
		results.add(SmtUtils.and(script, projected, update.effect().getFormula()));
	}

	private static Term forgetChangedConjuncts(final Term formula, final Set<TermVariable> changedVars,
			final Script script) {
		final Term[] conjuncts = SmtUtils.getConjuncts(formula);
		final Term[] kept = Stream.of(conjuncts)
				.filter(conjunct -> Stream.of(conjunct.getFreeVars()).noneMatch(changedVars::contains))
				.toArray(Term[]::new);
		return kept.length == conjuncts.length ? formula
				: kept.length == 0 ? script.term("true") : kept.length == 1 ? kept[0] : SmtUtils.and(script, kept);
	}

	private static Set<TermVariable> mergeModifiedGlobals(final GuardedUpdate left, final GuardedUpdate right) {
		if (left.modifiedGlobalsOrEmpty().isEmpty() || right.modifiedGlobalsOrEmpty().isEmpty()) {
			return Set.of();
		}
		return Stream.concat(left.modifiedGlobalsOrEmpty().stream(), right.modifiedGlobalsOrEmpty().stream())
				.collect(Collectors.toUnmodifiableSet());
	}
}
