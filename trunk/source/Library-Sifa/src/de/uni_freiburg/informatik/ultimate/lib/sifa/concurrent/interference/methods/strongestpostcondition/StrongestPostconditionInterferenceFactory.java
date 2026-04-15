package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition;

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

public final class StrongestPostconditionInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeTraverser mTraverser;
	private final TransFormulaToInterferencePredicate mTranslator;
	private final RelationalPredicatePostcondition mPostcondition;
	private final BasicPredicateFactory mPredicateFactory;
	private final ManagedScript mManagedScript;

	public StrongestPostconditionInterferenceFactory(final InterferenceEdgeTraverser traverser,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final BasicPredicateFactory predicateFactory, final ManagedScript managedScript) {
		mTraverser = traverser;
		mTranslator = translator;
		mPostcondition = postcondition;
		mPredicateFactory = predicateFactory;
		mManagedScript = managedScript;
	}

	@Override
	public IInterference createEmpty() {
		return new StrongestPostconditionInterference(Map.of(), mPostcondition);
	}

	@Override
	public IInterference buildFromStates(final String threadId, final Map<IcfgLocation, IPredicate> locationStates) {
		final Map<AbstractLocationPair, StrongestPostconditionInterference.RelationalInterference>
				interferenceByAbstractLocationPair = new LinkedHashMap<>();
		for (final InterferenceEdge edge : mTraverser.collect(locationStates)) {
			final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(edge.sourceState());
			final IPredicate relationalInterference =
					InterferenceMethodHelpers.combine(sharedPreState, edge.transitionPredicate(), mManagedScript,
							mPredicateFactory);
			if (InterferenceMethodHelpers.shouldSkipTrivialPredicate(relationalInterference)) {
				continue;
			}
			final var relationalInterferenceForEdge = new StrongestPostconditionInterference.RelationalInterference(
					relationalInterference, mPostcondition.prepareRelation(relationalInterference));
			interferenceByAbstractLocationPair.merge(edge.abstractLocationPair(), relationalInterferenceForEdge,
					this::mergeRelationalInterferences);
		}
		return new StrongestPostconditionInterference(interferenceByAbstractLocationPair, mPostcondition);
	}

	private StrongestPostconditionInterference.RelationalInterference mergeRelationalInterferences(
			final StrongestPostconditionInterference.RelationalInterference left,
			final StrongestPostconditionInterference.RelationalInterference right) {
		final IPredicate mergedRelationalInterference = InterferenceMethodHelpers.or(left.relationalInterference(),
				right.relationalInterference(), mManagedScript, mPredicateFactory);
		return new StrongestPostconditionInterference.RelationalInterference(mergedRelationalInterference,
				mPostcondition.prepareRelation(mergedRelationalInterference));
	}
}
