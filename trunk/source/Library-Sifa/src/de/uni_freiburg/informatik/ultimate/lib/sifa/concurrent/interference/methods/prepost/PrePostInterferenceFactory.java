package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.prepost;

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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
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
	public IInterference buildFromStates(final String threadId, final Map<IcfgLocation, IPredicate> locationStates) {
		final Map<AbstractLocationPair, PrePostInterference.PrePostPair> interferenceByAbstractLocationPair =
				new LinkedHashMap<>();
		for (final TranslatedInterferenceOfEdge edge : mTraverser.collect(locationStates)) {
			final IPredicate sourceState = locationStates.get(edge.source());
			if (sourceState == null) {
				continue;
			}
			final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(sourceState);
			final IPredicate relationalInterference = combine(sharedPreState, edge.transitionPredicate());
			if (shouldSkipTrivialPredicate(relationalInterference)) {
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
		return interferenceByAbstractLocationPair.isEmpty() ? null
				: new PrePostInterference(interferenceByAbstractLocationPair, mManagedScript);
	}

	private PrePostInterference.PrePostPair mergePairs(final PrePostInterference.PrePostPair left,
			final PrePostInterference.PrePostPair right) {
		return new PrePostInterference.PrePostPair(or(left.preState(), right.preState()),
				or(left.postState(), right.postState()));
	}

	private IPredicate combine(final IPredicate left, final IPredicate right) {
		final Term combined = SmtUtils.andWithExtendedLocalSimplification(mManagedScript.getScript(),
				left.getFormula(), right.getFormula());
		return mPredicateFactory.newPredicate(combined);
	}

	private IPredicate or(final IPredicate left, final IPredicate right) {
		final Script script = mManagedScript.getScript();
		return mPredicateFactory.newPredicate(SmtUtils.or(script, left.getFormula(), right.getFormula()));
	}

	private static boolean shouldSkipTrivialPredicate(final IPredicate predicate) {
		return SmtUtils.isTrueLiteral(predicate.getFormula()) || SmtUtils.isFalseLiteral(predicate.getFormula());
	}
}
