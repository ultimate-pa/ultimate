package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.unaryglobals;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GroupedInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeCollector;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.TranslatedInterferenceOfEdge;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class UnaryGlobalInterferenceFactory
		extends GroupedInterferenceFactory<Map<String, Map<IProgramVar, IPredicate>>> {

	private final IUltimateServiceProvider mServices;
	private final IDomain mDomain;

	public UnaryGlobalInterferenceFactory(final InterferenceEdgeCollector edgeCollector,
			final IUltimateServiceProvider services, final TransFormulaToInterferencePredicate translator,
			final RelationalPredicatePostcondition postcondition, final IDomain domain,
			final BasicPredicateFactory predicateFactory, final ManagedScript managedScript,
			final MustLocksetAnalysis locksetInfo) {
		super(edgeCollector, translator, postcondition, managedScript, predicateFactory, locksetInfo, Map.of());
		mServices = services;
		mDomain = domain;
	}

	@Override
	protected Map<String, Map<IProgramVar, IPredicate>> createAccumulator() {
		return new LinkedHashMap<>();
	}

	@Override
	protected void accumulateEdgeSummary(final Map<String, Map<IProgramVar, IPredicate>> accumulator,
			final TranslatedInterferenceOfEdge edge, final Map<IcfgLocation, IPredicate> threadStates) {
		final IPredicate postState = computeEdgeLocalPostState(edge, threadStates);
		if (postState == null || SmtUtils.isFalseLiteral(postState.getFormula())) {
			return;
		}
		final Map<IProgramVar, IPredicate> threadSummary =
				accumulator.computeIfAbsent(edge.source().getProcedure(), k -> new LinkedHashMap<>());
		for (final IProgramVar global : edge.changedGlobals()) {
			final IPredicate unarySummary = SmtUtils.isTrueLiteral(postState.getFormula()) ? mTruePredicate
					: projectToSingleGlobal(postState, global);
			threadSummary.merge(global, unarySummary, mDomain::join);
		}
	}

	@Override
	protected IInterferenceSet buildInterferenceSet(final Map<String, Map<IProgramVar, IPredicate>> accumulator) {
		return accumulator.isEmpty() ? null
				: UnaryGlobalInterference.create(accumulator, mServices, mManagedScript, mPredicateFactory);
	}

	private IPredicate computeEdgeLocalPostState(final TranslatedInterferenceOfEdge edge,
			final Map<IcfgLocation, IPredicate> threadStates) {
		final IPredicate sourceState = threadStates.get(edge.source());
		if (sourceState == null || SmtUtils.isFalseLiteral(sourceState.getFormula())) {
			return mFalsePredicate;
		}
		final IPredicate relationalInterference = conjoin(sourceState, edge.transitionPredicate());
		return unconditionalPostStateOf(relationalInterference);
	}

	private IPredicate projectToSingleGlobal(final IPredicate sharedState, final IProgramVar global) {
		final Set<TermVariable> varsToForget = new HashSet<>();
		sharedState.getVars().stream().filter(var -> !var.equals(global)).map(IProgramVar::getTermVariable)
				.forEach(varsToForget::add);
		final Term projected = varsToForget.isEmpty() || !containsAny(sharedState.getFormula(), varsToForget)
				? sharedState.getFormula()
				: RelationalPredicateUtils.existentiallyProject(sharedState.getFormula(), varsToForget, mServices,
						mManagedScript);
		return mPredicateFactory.newPredicate(projected);
	}

	private static boolean containsAny(final Term term, final Set<TermVariable> candidates) {
		for (final TermVariable freeVar : term.getFreeVars()) {
			if (candidates.contains(freeVar)) {
				return true;
			}
		}
		return false;
	}
}
