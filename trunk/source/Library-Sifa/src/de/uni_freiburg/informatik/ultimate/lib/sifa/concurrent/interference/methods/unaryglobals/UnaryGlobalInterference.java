package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.unaryglobals;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.IThreadLocalDomainContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * A very coarse interference abstraction that keeps one unary summary predicate per changed global variable,
 * stored per-thread for precise filtering and convergence checking.
 */
public final class UnaryGlobalInterference implements IInterference {

	/** Precomputed per-thread data for fast application. */
	private record PerThreadData(
			Map<IProgramVar, IPredicate> summaryByGlobal,
			Set<TermVariable> varsToForget,
			Term combinedSummary,
			IdentityHashMap<Term, Term> projectionCache) {

		PerThreadData(final Map<IProgramVar, IPredicate> summaryByGlobal, final Script script) {
			this(Map.copyOf(summaryByGlobal),
					summaryByGlobal.keySet().stream().map(IProgramVar::getTermVariable)
							.collect(Collectors.toUnmodifiableSet()),
					buildCombined(summaryByGlobal, script),
					new IdentityHashMap<>());
		}

		private static Term buildCombined(final Map<IProgramVar, IPredicate> summaryByGlobal, final Script script) {
			Term combined = script.term("true");
			for (final IPredicate s : summaryByGlobal.values()) {
				combined = SmtUtils.and(script, combined, s.getFormula());
			}
			return combined;
		}
	}

	// threadId → per-thread data; LinkedHashMap preserves insertion order for deterministic iteration
	private final Map<String, PerThreadData> mDataByThread;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;

	private UnaryGlobalInterference(final Map<String, PerThreadData> dataByThread,
			final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory) {
		mDataByThread = Map.copyOf(dataByThread);
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
	}

	public static UnaryGlobalInterference create(final Map<String, Map<IProgramVar, IPredicate>> summaryByThread,
			final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory) {
		final Map<String, PerThreadData> data = new LinkedHashMap<>();
		final Script script = managedScript.getScript();
		summaryByThread.forEach((threadId, summary) -> data.put(threadId, new PerThreadData(summary, script)));
		return new UnaryGlobalInterference(data, services, managedScript, predicateFactory);
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final Set<String> activeThreadIds,
			final IDomain domain, final int wideningThreshold, final SifaStats stats) {
		if (mDataByThread.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}
		final List<PerThreadData> filtered = buildFiltered(activeThreadIds);
		if (filtered.isEmpty()) {
			return state;
		}
		IPredicate current = state;
		for (final PerThreadData data : filtered) {
			current = domain.join(current, overwriteSummarizedGlobals(current, data));
		}
		return current;
	}

	private List<PerThreadData> buildFiltered(final Set<String> activeThreadIds) {
		final List<PerThreadData> filtered = new ArrayList<>();
		for (final Entry<String, PerThreadData> e : mDataByThread.entrySet()) {
			if (activeThreadIds.contains(e.getKey()) && !e.getValue().summaryByGlobal().isEmpty()) {
				filtered.add(e.getValue());
			}
		}
		return filtered;
	}

	private IPredicate overwriteSummarizedGlobals(final IPredicate state, final PerThreadData data) {
		final Term stateTerm = state.getFormula();
		final Term forgotten;
		if (data.varsToForget().isEmpty() || !hasAnyFreeVarIn(stateTerm, data.varsToForget())) {
			forgotten = stateTerm;
		} else {
			forgotten = data.projectionCache().computeIfAbsent(stateTerm,
					k -> RelationalPredicateUtils.existentiallyProject(k, data.varsToForget(), mServices,
							mManagedScript));
		}
		return mPredicateFactory
				.newPredicate(SmtUtils.and(mManagedScript.getScript(), forgotten, data.combinedSummary()));
	}

	@Override
	public boolean isEmpty() {
		return mDataByThread.isEmpty();
	}

	@Override
	public Set<String> threadIds() {
		return mDataByThread.keySet();
	}

	@Override
	public IInterference widen(final IInterference other, final IDomain domain) {
		if (!(other instanceof final UnaryGlobalInterference typedOther)) {
			throw new IllegalArgumentException(
					"Cannot widen UnaryGlobalInterference with " + other.getClass().getSimpleName());
		}
		final Map<String, Map<IProgramVar, IPredicate>> result = new LinkedHashMap<>();
		for (final Entry<String, PerThreadData> entry : mDataByThread.entrySet()) {
			IThreadLocalDomainContext.setIfApplicable(domain, entry.getKey());
			final PerThreadData otherData = typedOther.mDataByThread.get(entry.getKey());
			final Map<IProgramVar, IPredicate> widenedSummary = new LinkedHashMap<>();
			for (final Entry<IProgramVar, IPredicate> g : entry.getValue().summaryByGlobal().entrySet()) {
				final IPredicate otherSummary = otherData == null ? null : otherData.summaryByGlobal().get(g.getKey());
				widenedSummary.put(g.getKey(),
						otherSummary == null ? g.getValue() : domain.widen(g.getValue(), otherSummary));
			}
			if (!widenedSummary.isEmpty()) {
				result.put(entry.getKey(), widenedSummary);
			}
		}
		// Include threads present only in other (no widen needed, just copy)
		for (final Entry<String, PerThreadData> entry : typedOther.mDataByThread.entrySet()) {
			if (!result.containsKey(entry.getKey())) {
				result.put(entry.getKey(), new LinkedHashMap<>(entry.getValue().summaryByGlobal()));
			}
		}
		return result.isEmpty() ? null
				: UnaryGlobalInterference.create(result, mServices, mManagedScript, mPredicateFactory);
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		if (!(other instanceof final UnaryGlobalInterference typedOther)) {
			return false;
		}
		for (final Entry<String, PerThreadData> entry : mDataByThread.entrySet()) {
			IThreadLocalDomainContext.setIfApplicable(domain, entry.getKey());
			final PerThreadData otherData = typedOther.mDataByThread.get(entry.getKey());
			for (final Entry<IProgramVar, IPredicate> g : entry.getValue().summaryByGlobal().entrySet()) {
				final IPredicate otherSummary = otherData == null ? null : otherData.summaryByGlobal().get(g.getKey());
				if (otherSummary == null
						|| !domain.isSubsetEq(g.getValue(), otherSummary).isTrueForAbstraction()) {
					return false;
				}
			}
		}
		return true;
	}

	private static boolean hasAnyFreeVarIn(final Term term, final Set<TermVariable> candidates) {
		for (final TermVariable freeVar : term.getFreeVars()) {
			if (candidates.contains(freeVar)) {
				return true;
			}
		}
		return false;
	}
}
