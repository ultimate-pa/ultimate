package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.MLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.LoopLockstepOrder.PredicateWithLastThread;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class CoverageAnalysisSleepSetPOR<L extends IAction> {

	public static final Function<Object, Function<Object, Object>> DEFAULT_AGGREGATION =
			x -> y -> new BackwardCoveringInformation((BackwardCoveringInformation) x, (BackwardCoveringInformation) y);

	protected final IUltimateServiceProvider mServices;

	protected final ILogger mLogger;

	private final List<IPredicate> mStateSequence;
	private final IPredicateUnifier mPredicateUnifier;

	private final Map<Pair<IcfgLocation[], Set<L>>, List<Integer>> mState2Occurence = new HashMap<>();

	private int mUnsat;
	private int mSat;
	private int mUnknown;
	private int mTrivial;
	private int mNotchecked;

	protected final TracePredicates mIpp;

	public CoverageAnalysisSleepSetPOR(final IUltimateServiceProvider services, final TracePredicates ipp,
			final List<IPredicate> stateSequence, final ILogger logger, final IPredicateUnifier predicateUnifier) {
		mServices = services;
		mLogger = logger;
		mStateSequence = stateSequence;
		mPredicateUnifier = predicateUnifier;
		mIpp = ipp;
	}
	
	
	public void analyze() {
		assert mStateSequence.size() - 2 == mIpp.getPredicates().size() : "Wrong amount of interpolants";
		
		for (int i = 0; i < mStateSequence.size() - 1; i++) {
			final SleepPredicate<L> state = (SleepPredicate<L>) mStateSequence.get(i);
			IPredicate pred = state.getUnderlying();
			
			if (pred instanceof PredicateWithLastThread) {
				pred = ((PredicateWithLastThread) pred).getUnderlying();
			}
			ImmutableSet<L> sleepset = state.getAnnotation();
			IcfgLocation[] pp = ((IMLPredicate) pred).getProgramPoints();
			Pair<IcfgLocation[], Set<L>> pair = new Pair<>(pp, sleepset);
			List<Integer> previousOccurrences = mState2Occurence.get(pair);
					
			if (previousOccurrences == null) {
				previousOccurrences = new ArrayList<>();
				mState2Occurence.put(pair, previousOccurrences);
			} else {
				for (final int previousOccurrence : previousOccurrences) {
					assert i > previousOccurrence;
					final IPredicate currentPredicate = mIpp.getPredicate(i);
					final IPredicate previousPredicate = mIpp.getPredicate(previousOccurrence);
					if (currentPredicate == previousPredicate) {
						// trivially covered and backedges already contained
						mTrivial++;
					} else {
						final Validity lbool =
								mPredicateUnifier.getCoverageRelation().isCovered(currentPredicate, previousPredicate);
						switch (lbool) {
						case VALID:
							mUnsat++;
							break;
						case INVALID:
							mSat++;
							break;
						case UNKNOWN:
							mUnknown++;
							break;
						case NOT_CHECKED:
							mNotchecked++;
							break;
						default:
							throw new AssertionError();
						}
					}
				}
			}
			previousOccurrences.add(i);
		}
		assert sumCountedOccurrences() == mStateSequence.size() - 1;
	}
	
	private int sumCountedOccurrences() {
		int occurrenceSum = 0;
		for (final Entry<Pair<IcfgLocation[], Set<L>>, List<Integer>> entry : mState2Occurence.entrySet()) {
			occurrenceSum += entry.getValue().size();
		}
		return occurrenceSum;
	}
	
	public BackwardCoveringInformation getBackwardCoveringInformation() {
		final int potentialBackwardCoverings = mUnsat + mSat + mUnknown + mTrivial + mNotchecked;
		final int successfullBackwardCoverings = mUnsat + mTrivial;
		return new BackwardCoveringInformation(potentialBackwardCoverings, successfullBackwardCoverings);
	}
}
