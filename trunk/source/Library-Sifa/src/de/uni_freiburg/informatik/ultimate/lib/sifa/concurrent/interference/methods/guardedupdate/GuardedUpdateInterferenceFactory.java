package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.guardedupdate;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class GuardedUpdateInterferenceFactory implements IInterferenceFactory {

	private final GuardedUpdateEdgeTraverser mTraverser;
	private final TransFormulaToInterferencePredicate mTranslator;
	private final RelationalPredicatePostcondition mPostcondition;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final IPredicate mTruePredicate;

	public GuardedUpdateInterferenceFactory(final IIcfg<IcfgLocation> icfg,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory) {
		mTraverser = new GuardedUpdateEdgeTraverser(icfg, translator);
		mTranslator = translator;
		mPostcondition = postcondition;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mTruePredicate = predicateFactory.newPredicate(managedScript.getScript().term("true"));
	}

	@Override
	public IInterference buildFromStates(final String threadId, final Map<IcfgLocation, IPredicate> locationStates) {
		final Map<AbstractLocationPair, List<GuardedUpdate>> interferenceByAbstractLocationPair =
				new LinkedHashMap<>();
		for (final GuardedUpdateEdgeTraverser.GuardedUpdateEdge edge : mTraverser.collect(locationStates)) {
			final IPredicate sourceState = locationStates.get(edge.source());
			if (sourceState == null) {
				continue;
			}
			final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(sourceState);
			final GuardedUpdate update = tryCreateUpdate(edge, sharedPreState);
			if (update == null || shouldSkipTrivialPredicate(update.effect())) {
				continue;
			}
			interferenceByAbstractLocationPair.merge(edge.abstractLocationPair(), List.of(update),
					(left, right) -> java.util.stream.Stream.concat(left.stream(), right.stream()).toList());
		}
		final Map<AbstractLocationPair, GuardedUpdateInterference.GuardedUpdateGroup> merged = new LinkedHashMap<>();
		interferenceByAbstractLocationPair.forEach((abstractLocationPair, updates) -> merged.put(abstractLocationPair,
				new GuardedUpdateInterference.GuardedUpdateGroup(updates)));
		return merged.isEmpty() ? null : new GuardedUpdateInterference(merged, mManagedScript, mPredicateFactory);
	}

	private GuardedUpdate tryCreateUpdate(final GuardedUpdateEdgeTraverser.GuardedUpdateEdge edge,
			final IPredicate sharedPreState) {
		final IPredicate relationalInterference = combine(sharedPreState, edge.transitionPredicate());
		if (shouldSkipTrivialPredicate(relationalInterference)) {
			return null;
		}
		final IPredicate effect = mPostcondition.strongestPostcondition(mTruePredicate, relationalInterference);
		final IPredicate guard = GuardedUpdateUtils.extractTransitionAwareGuard(relationalInterference,
				mPostcondition.primedVariablesIn(relationalInterference), mManagedScript, mPredicateFactory);
		return new GuardedUpdate(guard, effect, edge.modifiedGlobals());
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
