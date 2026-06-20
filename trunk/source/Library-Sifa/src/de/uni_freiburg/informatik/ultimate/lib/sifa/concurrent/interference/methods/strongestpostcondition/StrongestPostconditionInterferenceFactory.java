package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition;

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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class StrongestPostconditionInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeTraverser mTraverser;
	private final TransFormulaToInterferencePredicate mTranslator;
	private final RelationalPredicatePostcondition mPostcondition;
	private final BasicPredicateFactory mPredicateFactory;
	private final ManagedScript mManagedScript;
	private final IPredicate mTruePredicate;

	public StrongestPostconditionInterferenceFactory(final InterferenceEdgeTraverser traverser,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final BasicPredicateFactory predicateFactory, final ManagedScript managedScript) {
		mTraverser = traverser;
		mTranslator = translator;
		mPostcondition = postcondition;
		mPredicateFactory = predicateFactory;
		mManagedScript = managedScript;
		mTruePredicate = predicateFactory.newPredicate(managedScript.getScript().term("true"));
	}

	@Override
	public IInterference buildFromAllStates(final Map<String, Map<IcfgLocation, IPredicate>> perThreadStates) {
		final Map<IcfgLocation, IPredicate> allStates = mergeStates(perThreadStates);
		final Map<ThreadedKey, StrongestPostconditionInterference.RelationalInterference> interferenceByKey =
				new LinkedHashMap<>();
		final Map<String, String> locationVarNameByThread = new LinkedHashMap<>();
		for (final TranslatedInterferenceOfEdge edge : mTraverser.collect(allStates)) {
			final String threadId = edge.source().getProcedure();
			final Map<IcfgLocation, IPredicate> threadStates = perThreadStates.get(threadId);
			if (threadStates == null) {
				continue;
			}
			final IPredicate sourceState = threadStates.get(edge.source());
			if (sourceState == null) {
				continue;
			}
			final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(sourceState);
			final IPredicate relationalInterference = combine(sharedPreState, edge.transitionPredicate());
			if (InterferenceUtils.shouldSkipTrivialPredicate(relationalInterference)) {
				continue;
			}
			final TermVariable locationVar = mTranslator.getLocationTermVarOrNull(threadId);
			if (locationVar != null) {
				locationVarNameByThread.put(threadId, locationVar.getName());
			}
			final IPredicate unconditionalPostState =
					mPostcondition.strongestPostcondition(mTruePredicate, relationalInterference);
			final var relationalInterferenceForEdge = new StrongestPostconditionInterference.RelationalInterference(
					relationalInterference, mPostcondition.prepareRelation(relationalInterference),
					unconditionalPostState);
			interferenceByKey.merge(new ThreadedKey(threadId, edge.abstractLocationPair()),
					relationalInterferenceForEdge, this::mergeRelationalInterferences);
		}
		return interferenceByKey.isEmpty() ? null
				: new StrongestPostconditionInterference(interferenceByKey, locationVarNameByThread, mPostcondition);
	}

	private StrongestPostconditionInterference.RelationalInterference mergeRelationalInterferences(
			final StrongestPostconditionInterference.RelationalInterference left,
			final StrongestPostconditionInterference.RelationalInterference right) {
		final IPredicate mergedRelationalInterference =
				or(left.relationalInterference(), right.relationalInterference());
		final IPredicate mergedPostState = or(left.unconditionalPostState(), right.unconditionalPostState());
		return new StrongestPostconditionInterference.RelationalInterference(mergedRelationalInterference,
				mPostcondition.prepareRelation(mergedRelationalInterference), mergedPostState);
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

	private static Map<IcfgLocation, IPredicate> mergeStates(
			final Map<String, Map<IcfgLocation, IPredicate>> perThreadStates) {
		final Map<IcfgLocation, IPredicate> merged = new LinkedHashMap<>();
		perThreadStates.values().forEach(merged::putAll);
		return merged;
	}
}
