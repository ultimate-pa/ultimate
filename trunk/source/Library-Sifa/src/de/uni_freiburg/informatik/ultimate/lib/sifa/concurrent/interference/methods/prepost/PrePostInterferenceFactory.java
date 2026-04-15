package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.prepost;

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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class PrePostInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeTraverser mTraverser;
	private final TransFormulaToInterferencePredicate mTranslator;
	private final RelationalPredicatePostcondition mPostcondition;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;

	public PrePostInterferenceFactory(final InterferenceEdgeTraverser traverser,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory) {
		mTraverser = traverser;
		mTranslator = translator;
		mPostcondition = postcondition;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
	}

	@Override
	public IInterference createEmpty() {
		return new PrePostInterference(Map.of(), mManagedScript);
	}

	@Override
	public IInterference buildFromStates(final String threadId, final Map<IcfgLocation, IPredicate> locationStates) {
		final Map<AbstractLocationPair, PrePostInterference.PrePostPair> interferenceByAbstractLocationPair =
				new LinkedHashMap<>();
		for (final InterferenceEdge edge : mTraverser.collect(locationStates)) {
			final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(edge.sourceState());
			final IPredicate relationalInterference =
					InterferenceMethodHelpers.combine(sharedPreState, edge.transitionPredicate(), mManagedScript,
							mPredicateFactory);
			if (InterferenceMethodHelpers.shouldSkipTrivialPredicate(relationalInterference)) {
				continue;
			}
			PrePostInterference.PrePostPair mergedPair = null;
			for (final Term preDisjunctTerm : SmtUtils.getDisjuncts(sharedPreState.getFormula())) {
				if (SmtUtils.isFalseLiteral(preDisjunctTerm)) {
					continue;
				}
				final IPredicate preDisjunct = mPredicateFactory.newPredicate(preDisjunctTerm);
				final IPredicate postState = mPostcondition.strongestPostcondition(preDisjunct, relationalInterference);
				if (!SmtUtils.isFalseLiteral(postState.getFormula())) {
					final var nextPair = new PrePostInterference.PrePostPair(preDisjunct, postState);
					mergedPair = mergedPair == null ? nextPair : mergePairs(mergedPair, nextPair);
				}
			}
			if (mergedPair != null) {
				interferenceByAbstractLocationPair.merge(edge.abstractLocationPair(), mergedPair, this::mergePairs);
			}
		}
		return new PrePostInterference(interferenceByAbstractLocationPair, mManagedScript);
	}

	private PrePostInterference.PrePostPair mergePairs(final PrePostInterference.PrePostPair left,
			final PrePostInterference.PrePostPair right) {
		return new PrePostInterference.PrePostPair(
				InterferenceMethodHelpers.or(left.preState(), right.preState(), mManagedScript, mPredicateFactory),
				InterferenceMethodHelpers.or(left.postState(), right.postState(), mManagedScript, mPredicateFactory));
	}
}
