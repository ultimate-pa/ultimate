package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.poststate;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdge;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeTraverser;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceMethodHelpers;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

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
	public IInterference createEmpty() {
		return new PostStateInterference(Map.of());
	}

	@Override
	public IInterference buildFromStates(final String threadId, final Map<IcfgLocation, IPredicate> locationStates) {
		final Map<AbstractLocationPair, IPredicate> interferenceByAbstractLocationPair = new LinkedHashMap<>();
		final Map<IcfgLocation, IPredicate> sharedTargetStates = new LinkedHashMap<>();
		for (final InterferenceEdge edge : mTraverser.collect(locationStates)) {
			final IPredicate sharedTargetState = getSharedTargetState(edge.target(), locationStates, sharedTargetStates);
			final IPredicate postState = sharedTargetState != null ? sharedTargetState : computeEdgeLocalPostState(edge);
			if (InterferenceMethodHelpers.shouldSkipTrivialPredicate(postState)) {
				continue;
			}
			interferenceByAbstractLocationPair.merge(edge.abstractLocationPair(), postState, mDomain::join);
		}
		return new PostStateInterference(interferenceByAbstractLocationPair);
	}

	private IPredicate getSharedTargetState(final IcfgLocation target, final Map<IcfgLocation, IPredicate> locationStates,
			final Map<IcfgLocation, IPredicate> sharedTargetStates) {
		if (!sharedTargetStates.containsKey(target)) {
			final IPredicate targetState = locationStates.get(target);
			sharedTargetStates.put(target, targetState == null ? null : mTranslator.projectPreStateToSharedState(targetState));
		}
		return sharedTargetStates.get(target);
	}

	private IPredicate computeEdgeLocalPostState(final InterferenceEdge edge) {
		final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(edge.sourceState());
		final IPredicate relationalInterference =
				InterferenceMethodHelpers.combine(sharedPreState, edge.transitionPredicate(), mManagedScript,
						mPredicateFactory);
		if (InterferenceMethodHelpers.shouldSkipTrivialPredicate(relationalInterference)) {
			return relationalInterference;
		}
		return mPostcondition.strongestPostcondition(mTruePredicate, relationalInterference);
	}
}
