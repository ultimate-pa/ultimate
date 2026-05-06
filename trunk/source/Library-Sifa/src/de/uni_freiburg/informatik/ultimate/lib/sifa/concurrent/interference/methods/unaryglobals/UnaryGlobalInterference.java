package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.unaryglobals;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
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
 * A very coarse interference abstraction that keeps one unary summary predicate per changed global variable.
 */
public final class UnaryGlobalInterference implements IInterference {

	private final Map<IProgramVar, IPredicate> mSummaryByGlobal;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;

	public UnaryGlobalInterference(final Map<IProgramVar, IPredicate> summaryByGlobal,
			final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory) {
		mSummaryByGlobal = Map.copyOf(summaryByGlobal);
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final IDomain domain, final int wideningThreshold,
			final SifaStats stats) {
		if (mSummaryByGlobal.isEmpty()) {
			return state;
		}
		IPredicate current = state;
		while (true) {
			final IPredicate overwritten = overwriteSummarizedGlobals(current);
			final IPredicate next = domain.join(current, overwritten);
			if (domain.isSubsetEq(next, current).isTrueForAbstraction()) {
				return current;
			}
			current = next;
		}
	}

	private IPredicate overwriteSummarizedGlobals(final IPredicate state) {
		final Set<TermVariable> varsToForget = mSummaryByGlobal.keySet().stream().map(IProgramVar::getTermVariable)
				.collect(Collectors.toSet());
		final Script script = mManagedScript.getScript();
		final Term forgotten = varsToForget.isEmpty() || !hasAnyFreeVarIn(state.getFormula(), varsToForget)
						? state.getFormula()
						: RelationalPredicateUtils.existentiallyProject(state.getFormula(), varsToForget, mServices,
								mManagedScript);

		Term combined = forgotten;
		for (final IPredicate unarySummary : mSummaryByGlobal.values()) {
			combined = SmtUtils.and(script, combined, unarySummary.getFormula());
		}
		return mPredicateFactory.newPredicate(combined);
	}

	@Override
	public IInterference widen(final IInterference other, final IDomain domain) {
		if (!(other instanceof final UnaryGlobalInterference typedOther)) {
			throw new IllegalArgumentException(
					"Cannot widen UnaryGlobalInterference with " + other.getClass().getSimpleName());
		}
		final Map<IProgramVar, IPredicate> widened = new LinkedHashMap<>();
		for (final Entry<IProgramVar, IPredicate> entry : mSummaryByGlobal.entrySet()) {
			final IPredicate otherSummary = typedOther.mSummaryByGlobal.get(entry.getKey());
			final IPredicate widenedSummary = otherSummary == null ? entry.getValue()
					: domain.widen(entry.getValue(), otherSummary);
			widened.put(entry.getKey(), widenedSummary);
		}
		for (final Entry<IProgramVar, IPredicate> entry : typedOther.mSummaryByGlobal.entrySet()) {
			widened.putIfAbsent(entry.getKey(), entry.getValue());
		}
		return widened.isEmpty() ? null
				: new UnaryGlobalInterference(widened, mServices, mManagedScript, mPredicateFactory);
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		if (!(other instanceof final UnaryGlobalInterference typedOther)) {
			return false;
		}
		for (final Entry<IProgramVar, IPredicate> entry : mSummaryByGlobal.entrySet()) {
			final IPredicate otherSummary = typedOther.mSummaryByGlobal.get(entry.getKey());
			if (otherSummary == null || !domain.isSubsetEq(entry.getValue(), otherSummary).isTrueForAbstraction()) {
				return false;
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
