package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.guardedupdate;

import java.util.LinkedHashMap;
import java.util.List;
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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

public final class GuardedUpdateInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeTraverser mTraverser;
	private final TransFormulaToInterferencePredicate mTranslator;
	private final RelationalPredicatePostcondition mPostcondition;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final IPredicate mTruePredicate;

	public GuardedUpdateInterferenceFactory(final InterferenceEdgeTraverser traverser,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory) {
		mTraverser = traverser;
		mTranslator = translator;
		mPostcondition = postcondition;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mTruePredicate = predicateFactory.newPredicate(managedScript.getScript().term("true"));
	}

	@Override
	public IInterference createEmpty() {
		return new GuardedUpdateInterference(Map.of(), mManagedScript, mPredicateFactory);
	}

	@Override
	public IInterference buildFromStates(final String threadId, final Map<IcfgLocation, IPredicate> locationStates) {
		final Map<AbstractLocationPair, List<GuardedUpdate>> interferenceByAbstractLocationPair =
				new LinkedHashMap<>();
		for (final InterferenceEdge edge : mTraverser.collect(locationStates)) {
			final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(edge.sourceState());
			final GuardedUpdate update = tryCreateUpdate(edge, sharedPreState);
			if (update == null || InterferenceMethodHelpers.shouldSkipTrivialPredicate(update.effect())) {
				continue;
			}
			interferenceByAbstractLocationPair.merge(edge.abstractLocationPair(), List.of(update),
					(left, right) -> java.util.stream.Stream.concat(left.stream(), right.stream()).toList());
		}
		final Map<AbstractLocationPair, GuardedUpdateInterference.GuardedUpdateGroup> merged = new LinkedHashMap<>();
		interferenceByAbstractLocationPair.forEach((abstractLocationPair, updates) -> merged.put(abstractLocationPair,
				new GuardedUpdateInterference.GuardedUpdateGroup(updates)));
		return new GuardedUpdateInterference(merged, mManagedScript, mPredicateFactory);
	}

	private GuardedUpdate tryCreateUpdate(final InterferenceEdge edge, final IPredicate sharedPreState) {
		final IPredicate relationalInterference =
				InterferenceMethodHelpers.combine(sharedPreState, edge.transitionPredicate(), mManagedScript,
						mPredicateFactory);
		if (InterferenceMethodHelpers.shouldSkipTrivialPredicate(relationalInterference)) {
			return null;
		}
		final IPredicate effect = mPostcondition.strongestPostcondition(mTruePredicate, relationalInterference);
		final IPredicate guard = GuardedUpdateUtils.extractTransitionAwareGuard(relationalInterference,
				mPostcondition.primedVariablesIn(relationalInterference), mManagedScript, mPredicateFactory);
		return new GuardedUpdate(guard, effect, edge.modifiedGlobals());
	}
}
