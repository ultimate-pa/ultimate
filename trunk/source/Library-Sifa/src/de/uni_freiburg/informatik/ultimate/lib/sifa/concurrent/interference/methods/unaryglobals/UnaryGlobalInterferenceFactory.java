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
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeTraverser;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.TranslatedInterferenceOfEdge;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class UnaryGlobalInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeTraverser mTraverser;
	private final IUltimateServiceProvider mServices;
	private final RelationalPredicatePostcondition mPostcondition;
	private final IDomain mDomain;
	private final BasicPredicateFactory mPredicateFactory;
	private final ManagedScript mManagedScript;
	private final IPredicate mTruePredicate;
	private final IPredicate mFalsePredicate;

	public UnaryGlobalInterferenceFactory(final InterferenceEdgeTraverser traverser,
			final IUltimateServiceProvider services, final TransFormulaToInterferencePredicate translator,
			final RelationalPredicatePostcondition postcondition, final IDomain domain,
			final BasicPredicateFactory predicateFactory, final ManagedScript managedScript) {
		mTraverser = traverser;
		mServices = services;
		mPostcondition = postcondition;
		mDomain = domain;
		mPredicateFactory = predicateFactory;
		mManagedScript = managedScript;
		mTruePredicate = predicateFactory.newPredicate(managedScript.getScript().term("true"));
		mFalsePredicate = predicateFactory.newPredicate(managedScript.getScript().term("false"));
	}

	@Override
	public IInterference buildFromAllStates(final Map<String, Map<IcfgLocation, IPredicate>> perThreadStates) {
		final Map<IcfgLocation, IPredicate> allStates = mergeStates(perThreadStates);
		// threadId → (global → summary predicate)
		final Map<String, Map<IProgramVar, IPredicate>> summaryByThread = new LinkedHashMap<>();
		for (final TranslatedInterferenceOfEdge edge : mTraverser.collect(allStates)) {
			if (edge.changedGlobals().isEmpty()) {
				continue;
			}
			final String threadId = edge.source().getProcedure();
			final Map<IcfgLocation, IPredicate> threadStates = perThreadStates.get(threadId);
			if (threadStates == null) {
				continue;
			}
			final IPredicate postState = computeEdgeLocalPostState(edge, threadStates);
			if (postState == null || SmtUtils.isFalseLiteral(postState.getFormula())) {
				continue;
			}
			final Map<IProgramVar, IPredicate> threadSummary =
					summaryByThread.computeIfAbsent(threadId, k -> new LinkedHashMap<>());
			for (final IProgramVar global : edge.changedGlobals()) {
				final IPredicate unarySummary = SmtUtils.isTrueLiteral(postState.getFormula()) ? mTruePredicate
						: projectToSingleGlobal(postState, global);
				threadSummary.merge(global, unarySummary, mDomain::join);
			}
		}
		return summaryByThread.isEmpty() ? null
				: UnaryGlobalInterference.create(summaryByThread, mServices, mManagedScript, mPredicateFactory);
	}

	private IPredicate computeEdgeLocalPostState(final TranslatedInterferenceOfEdge edge,
			final Map<IcfgLocation, IPredicate> threadStates) {
		final IPredicate sourceState = threadStates.get(edge.source());
		if (sourceState == null || SmtUtils.isFalseLiteral(sourceState.getFormula())) {
			return mFalsePredicate;
		}
		final Term combined = SmtUtils.andWithExtendedLocalSimplification(mManagedScript.getScript(),
				sourceState.getFormula(), edge.transitionPredicate().getFormula());
		final IPredicate relationalInterference = mPredicateFactory.newPredicate(combined);
		return mPostcondition.strongestPostcondition(mTruePredicate, relationalInterference);
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

	private static Map<IcfgLocation, IPredicate> mergeStates(
			final Map<String, Map<IcfgLocation, IPredicate>> perThreadStates) {
		final Map<IcfgLocation, IPredicate> merged = new LinkedHashMap<>();
		perThreadStates.values().forEach(merged::putAll);
		return merged;
	}
}
