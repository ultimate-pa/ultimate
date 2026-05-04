package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.BucketContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeTraverser;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.TranslatedInterferenceOfEdge;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class StrongestPostconditionInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeTraverser mTraverser;
	private final TransFormulaToInterferencePredicate mTranslator;
	private final RelationalPredicatePostcondition mPostcondition;
	private final BasicPredicateFactory mPredicateFactory;
	private final ManagedScript mManagedScript;
	private final BucketContext mBucketContext;

	public StrongestPostconditionInterferenceFactory(final InterferenceEdgeTraverser traverser,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final BasicPredicateFactory predicateFactory, final ManagedScript managedScript,
			final BucketContext bucketContext) {
		mTraverser = traverser;
		mTranslator = translator;
		mPostcondition = postcondition;
		mPredicateFactory = predicateFactory;
		mManagedScript = managedScript;
		mBucketContext = bucketContext;
	}

	@Override
	public IInterference buildFromStates(final Map<IcfgLocation, IPredicate> locationStates) {
		final Map<AbstractLocationPair, StrongestPostconditionInterference.RelationalInterference>
				interferenceByAbstractLocationPair = new LinkedHashMap<>();
		for (final TranslatedInterferenceOfEdge edge : mTraverser.collect(locationStates)) {
			final IPredicate sourceState = locationStates.get(edge.source());
			if (sourceState == null) {
				continue;
			}
			final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(sourceState);
			final IPredicate relationalInterference = combine(sharedPreState, edge.transitionPredicate());
			if (InterferenceUtils.shouldSkipTrivialPredicate(relationalInterference)) {
				continue;
			}
			final var relationalInterferenceForEdge = new StrongestPostconditionInterference.RelationalInterference(
					relationalInterference, mPostcondition.prepareRelation(relationalInterference));
			interferenceByAbstractLocationPair.merge(edge.abstractLocationPair(), relationalInterferenceForEdge,
					this::mergeRelationalInterferences);
		}
		return interferenceByAbstractLocationPair.isEmpty() ? null
				: new StrongestPostconditionInterference(interferenceByAbstractLocationPair, mPostcondition,
						mBucketContext);
	}

	private StrongestPostconditionInterference.RelationalInterference mergeRelationalInterferences(
			final StrongestPostconditionInterference.RelationalInterference left,
			final StrongestPostconditionInterference.RelationalInterference right) {
		final IPredicate mergedRelationalInterference =
				or(left.relationalInterference(), right.relationalInterference());
		return new StrongestPostconditionInterference.RelationalInterference(mergedRelationalInterference,
				mPostcondition.prepareRelation(mergedRelationalInterference));
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
}
