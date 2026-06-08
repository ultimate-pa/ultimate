package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.poststate;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeTraverser;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.ThreadedKey;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
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
	private final IPredicate mFalsePredicate;

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
		mFalsePredicate = predicateFactory.newPredicate(managedScript.getScript().term("false"));
	}

	@Override
	public IInterference buildFromAllStates(final Map<String, Map<IcfgLocation, IPredicate>> perThreadStates) {
		final Map<IcfgLocation, IPredicate> allStates = mergeStates(perThreadStates);
		final Map<ThreadedKey, IPredicate> interferenceByKey = new LinkedHashMap<>();
		for (final TranslatedInterferenceOfEdge edge : mTraverser.collect(allStates)) {
			final String threadId = edge.source().getProcedure();
			final Map<IcfgLocation, IPredicate> threadStates = perThreadStates.get(threadId);
			if (threadStates == null) {
				continue;
			}
			final IPredicate targetState = threadStates.get(edge.target());
			final IPredicate postState = targetState == null
					? computeEdgeLocalPostState(edge, threadStates) : mTranslator.projectPreStateToSharedState(targetState);
			if (InterferenceUtils.shouldSkipTrivialPredicate(postState)) {
				continue;
			}
			interferenceByKey.merge(new ThreadedKey(threadId, edge.abstractLocationPair()), postState, mDomain::join);
		}
		return interferenceByKey.isEmpty() ? null : new PostStateInterference(interferenceByKey);
	}

	private IPredicate computeEdgeLocalPostState(final TranslatedInterferenceOfEdge edge,
			final Map<IcfgLocation, IPredicate> threadStates) {
		final IPredicate sourceState = threadStates.get(edge.source());
		if (sourceState == null) {
			return mFalsePredicate;
		}
		final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(sourceState);
		final IPredicate relationalInterference = combine(sharedPreState, edge.transitionPredicate());
		if (InterferenceUtils.shouldSkipTrivialPredicate(relationalInterference)) {
			return relationalInterference;
		}
		return mPostcondition.strongestPostcondition(mTruePredicate, relationalInterference);
	}

	private IPredicate combine(final IPredicate left, final IPredicate right) {
		final Term combined = SmtUtils.andWithExtendedLocalSimplification(mManagedScript.getScript(),
				left.getFormula(), right.getFormula());
		return mPredicateFactory.newPredicate(combined);
	}

	private static Map<IcfgLocation, IPredicate> mergeStates(
			final Map<String, Map<IcfgLocation, IPredicate>> perThreadStates) {
		final Map<IcfgLocation, IPredicate> merged = new LinkedHashMap<>();
		perThreadStates.values().forEach(merged::putAll);
		return merged;
	}
}
