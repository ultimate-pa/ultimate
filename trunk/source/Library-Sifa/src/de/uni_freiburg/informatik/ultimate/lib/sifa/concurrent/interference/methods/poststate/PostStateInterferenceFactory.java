package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.poststate;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeTraverser;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.TranslatedInterferenceOfEdge;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class PostStateInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeTraverser mTraverser;
	private final TransFormulaToInterferencePredicate mTranslator;
	private final RelationalPredicatePostcondition mPostcondition;
	private final IDomain mDomain;
	private final BasicPredicateFactory mPredicateFactory;
	private final ManagedScript mManagedScript;
	private final IPredicate mTruePredicate;

	public PostStateInterferenceFactory(final InterferenceEdgeTraverser traverser,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final IDomain domain, final BasicPredicateFactory predicateFactory, final ManagedScript managedScript) {
		mTraverser = traverser;
		mTranslator = translator;
		mPostcondition = postcondition;
		mDomain = domain;
		mPredicateFactory = predicateFactory;
		mManagedScript = managedScript;
		mTruePredicate = predicateFactory.newPredicate(managedScript.getScript().term("true"));
	}

	@Override
	public IInterference buildFromStates(final String threadId, final Map<IcfgLocation, IPredicate> locationStates) {
		final Map<AbstractLocationPair, IPredicate> interferenceByAbstractLocationPair = new LinkedHashMap<>();
		final Map<IcfgLocation, IPredicate> sharedTargetStates = new LinkedHashMap<>();
		for (final TranslatedInterferenceOfEdge edge : mTraverser.collect(locationStates)) {
			final IPredicate sharedTargetState = getSharedTargetState(edge.target(), locationStates, sharedTargetStates);
			final IPredicate postState =
					sharedTargetState != null ? sharedTargetState : computeEdgeLocalPostState(edge, locationStates);
			if (shouldSkipTrivialPredicate(postState)) {
				continue;
			}
			interferenceByAbstractLocationPair.merge(edge.abstractLocationPair(), postState, mDomain::join);
		}
		return interferenceByAbstractLocationPair.isEmpty() ? null : new PostStateInterference(interferenceByAbstractLocationPair);
	}

	private IPredicate getSharedTargetState(final IcfgLocation target, final Map<IcfgLocation, IPredicate> locationStates,
			final Map<IcfgLocation, IPredicate> sharedTargetStates) {
		if (!sharedTargetStates.containsKey(target)) {
			final IPredicate targetState = locationStates.get(target);
			sharedTargetStates.put(target, targetState == null ? null : mTranslator.projectPreStateToSharedState(targetState));
		}
		return sharedTargetStates.get(target);
	}

	private IPredicate computeEdgeLocalPostState(final TranslatedInterferenceOfEdge edge,
			final Map<IcfgLocation, IPredicate> locationStates) {
		final IPredicate sourceState = locationStates.get(edge.source());
		if (sourceState == null) {
			return null;
		}
		final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(sourceState);
		final IPredicate relationalInterference = combine(sharedPreState, edge.transitionPredicate());
		if (shouldSkipTrivialPredicate(relationalInterference)) {
			return relationalInterference;
		}
		return mPostcondition.strongestPostcondition(mTruePredicate, relationalInterference);
	}

	private IPredicate combine(final IPredicate left, final IPredicate right) {
		final Term combined = SmtUtils.andWithExtendedLocalSimplification(mManagedScript.getScript(),
				left.getFormula(), right.getFormula());
		return mPredicateFactory.newPredicate(combined);
	}

	private static boolean shouldSkipTrivialPredicate(final IPredicate predicate) {
		return SmtUtils.isTrueLiteral(predicate.getFormula()) || SmtUtils.isFalseLiteral(predicate.getFormula());
	}
}
