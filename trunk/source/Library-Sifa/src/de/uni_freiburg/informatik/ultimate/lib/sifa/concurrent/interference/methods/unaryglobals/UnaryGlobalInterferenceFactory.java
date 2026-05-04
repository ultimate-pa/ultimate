package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.unaryglobals;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeTraverser;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
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
	private final TransFormulaToInterferencePredicate mTranslator;
	private final RelationalPredicatePostcondition mPostcondition;
	private final IDomain mDomain;
	private final BasicPredicateFactory mPredicateFactory;
	private final ManagedScript mManagedScript;
	private final IPredicate mTruePredicate;
	private final IPredicate mFalsePredicate;

	public UnaryGlobalInterferenceFactory(final InterferenceEdgeTraverser traverser,
			final IUltimateServiceProvider services,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final IDomain domain,
			final BasicPredicateFactory predicateFactory, final ManagedScript managedScript) {
		mTraverser = traverser;
		mServices = services;
		mTranslator = translator;
		mPostcondition = postcondition;
		mDomain = domain;
		mPredicateFactory = predicateFactory;
		mManagedScript = managedScript;
		mTruePredicate = predicateFactory.newPredicate(managedScript.getScript().term("true"));
		mFalsePredicate = predicateFactory.newPredicate(managedScript.getScript().term("false"));
	}

	@Override
	public IInterference buildFromStates(final Map<IcfgLocation, IPredicate> locationStates) {
		final Map<IProgramVar, IPredicate> summaryByGlobal = new LinkedHashMap<>();
		for (final TranslatedInterferenceOfEdge edge : mTraverser.collect(locationStates)) {
			if (edge.changedGlobals().isEmpty()) {
				continue;
			}
			final IPredicate postState = computeEdgeLocalPostState(edge, locationStates);
			if (InterferenceUtils.shouldSkipTrivialPredicate(postState)) {
				continue;
			}
			for (final IProgramVar global : edge.changedGlobals()) {
				final IPredicate unarySummary = projectToSingleGlobal(postState, global);
				summaryByGlobal.merge(global, unarySummary, mDomain::join);
			}
		}
		return summaryByGlobal.isEmpty() ? null
				: new UnaryGlobalInterference(summaryByGlobal, mServices, mManagedScript, mPredicateFactory);
	}

	private IPredicate computeEdgeLocalPostState(final TranslatedInterferenceOfEdge edge,
			final Map<IcfgLocation, IPredicate> locationStates) {
		final IPredicate sourceState = locationStates.get(edge.source());
		if (sourceState == null) {
			return mFalsePredicate;
		}
		final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(sourceState);
		final Term combined = SmtUtils.andWithExtendedLocalSimplification(mManagedScript.getScript(),
				sharedPreState.getFormula(), edge.transitionPredicate().getFormula());
		final IPredicate relationalInterference = mPredicateFactory.newPredicate(combined);
		if (InterferenceUtils.shouldSkipTrivialPredicate(relationalInterference)) {
			return relationalInterference;
		}
		return mPostcondition.strongestPostcondition(mTruePredicate, relationalInterference);
	}

	private IPredicate projectToSingleGlobal(final IPredicate sharedState, final IProgramVar global) {
		final Set<TermVariable> otherVars = sharedState.getVars().stream().filter(var -> !var.equals(global))
				.map(IProgramVar::getTermVariable).collect(Collectors.toSet());
		if (otherVars.isEmpty() || !containsAny(sharedState.getFormula(), otherVars)) {
			return sharedState;
		}
		final Term projected = RelationalPredicateUtils.existentiallyProject(sharedState.getFormula(), otherVars,
				mServices, mManagedScript);
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
