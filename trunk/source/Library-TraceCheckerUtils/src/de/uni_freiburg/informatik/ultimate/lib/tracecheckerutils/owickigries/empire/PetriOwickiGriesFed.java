package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.PlacesCoRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;
import de.uni_freiburg.informatik.ultimate.util.statistics.TimeTracker;

public class PetriOwickiGriesFed<L extends IAction, P> {
	public static final boolean IGNORE_CUTOFF_CONDITIONS = true;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final BasicPredicateFactory mFactory;

	private final IIcfgSymbolTable mSymbolTable;
	private final Set<String> mProcedures;
	private final ModifiableGlobalsTable mModifiableGlobals;

	private final IPetriNet<L, P> mNet;
	private final Set<P> mOriginalPlaces;
	private final List<Set<P>> mProofPlaces;

	private final BranchingProcess<L, P> mBp;
	private final Set<Condition<L, P>> mConditions;
	private final Set<Condition<L, P>> mOriginalConditions;
	private final Set<Condition<L, P>> mAssertionConditions;

	// private final Crown<PLACE, L> mCrown;
	private final Federation<P> mFederation;
	// private final OwickiGriesAnnotation<L, PLACE> mOwickiGriesAnnotation;

	private final Statistics mStatistics = new Statistics();

	/**
	 *
	 * @param bp
	 *            finite prefix of unfolding for the refined net
	 * @param net
	 *            the original Petri program
	 */
	public PetriOwickiGriesFed(final IUltimateServiceProvider services, final BranchingProcess<L, P> bp,
			final IPetriNet<L, P> net, final BasicPredicateFactory factory,
			final Function<P, IPredicate> placeToAssertion, final ManagedScript mgdScript,
			final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final ModifiableGlobalsTable modifiableGlobals, final List<Set<P>> proofPlaces) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(PetriOwickiGries.class);
		mMgdScript = mgdScript;
		mFactory = factory;

		mSymbolTable = symbolTable;
		mProcedures = procedures;
		mModifiableGlobals = modifiableGlobals;

		mNet = net;
		mOriginalPlaces = mNet.getPlaces();
		mProofPlaces = proofPlaces;

		mBp = bp;
		mConditions = getConditions();
		mOriginalConditions = getOrigConditions();
		mAssertionConditions = DataStructureUtils.difference(mConditions, mOriginalConditions);

		final long cutoffs = bp.getConditions().stream().filter(c -> c.getPredecessorEvent().isCutoffEvent()).count();
		mLogger.info(
				"Constructing Owicki-Gries proof for Petri program that %s and unfolding that %s."
						+ " %d conditions belong to cutoff events, %d conditions do not."
						+ " %d conditions are original conditions, %d conditions are assertion conditions.",
				net.sizeInformation(), bp.sizeInformation(), cutoffs, bp.getConditions().size() - cutoffs,
				mOriginalConditions.size(), mAssertionConditions.size());

		// mCrown = getCrown();
		// mLogger.info("Constructed Crown:\n%s", mCrown);
		final var placesCorelation = new PlacesCoRelation<>(mBp);
		final var computation = getFederationComputation(placeToAssertion, placesCorelation);
		mFederation = computation.getFederation();
		mLogger.info("Constructed Federation:\n%s", mFederation);
		assert checkFederationValidity(computation, placesCorelation) : "Federation is invalid";
	}

	public static final boolean isCutoff(final Condition<?, ?> cond) {
		return cond.getPredecessorEvent().isCutoffEvent();
	}

	public static <L, P> HashRelation<Transition<L, P>, P> getCoMarkedPlaces(final BranchingProcess<L, P> bp) {
		final HashRelation<Transition<L, P>, P> coMarkedPlaces = new HashRelation<>();
		final Collection<Condition<L, P>> conditions = bp.getConditions();
		final ICoRelation<L, P> coRelation = bp.getCoRelation();
		P place;
		Transition<L, P> transition;
		for (final Condition<L, P> condition : conditions) {
			place = condition.getPlace();
			for (final Event<L, P> event : coRelation.computeCoRelatatedEvents(condition)) {
				transition = event.getTransition();
				if (!transition.getPredecessors().contains(place)) {
					coMarkedPlaces.addPair(transition, place);
				}
			}
		}
		return coMarkedPlaces;
	}

	private FederationComputation<L, P> getFederationComputation(final Function<P, IPredicate> placeToAssertion,
			final PlacesCoRelation<P> placesCoRelation) {
		final var computation = new FederationComputation<>(mServices, mFactory, mBp.getNet(), mOriginalPlaces,
				mProofPlaces, placesCoRelation, placeToAssertion);
		mStatistics.reportFederationStatistics(computation);
		return computation;
	}

	private boolean checkFederationValidity(final FederationComputation<L, P> federationComputation,
			final PlacesCoRelation<P> placesCoRelation) {
		return mStatistics.measureFederationValidity(() -> {
			final var implicationChecker = new MonolithicImplicationChecker(mServices, mMgdScript);
			final var assertionPlaces = mProofPlaces.stream().flatMap(Set::stream).collect(Collectors.toSet());
			final var federation = federationComputation.getFederation();
			for (final EmpireAnnotation<P> empireAnnotation : federation.getEmpireAnnotations()) {
				final var checker = new EmpireValidityCheck<>(mServices, mMgdScript, implicationChecker, mFactory, mNet,
						mBp.getNet(), mModifiableGlobals, empireAnnotation,
						federationComputation.getPredicatePlaceMap(), assertionPlaces, placesCoRelation);
				if (checker.getValidity() != Validity.VALID) {
					return Validity.INVALID;
				}
			}
			return Validity.VALID;
		}) != Validity.INVALID;
	}

	private Set<Condition<L, P>> getConditions() {
		Set<Condition<L, P>> conditions;
		if (IGNORE_CUTOFF_CONDITIONS) {
			mLogger.info("Ignoring conditions belonging to cutoff events.");
			conditions = mBp.getConditions().stream().filter(c -> !isCutoff(c)).collect(Collectors.toSet());
		} else {
			conditions = mBp.getConditions().stream().collect(Collectors.toSet());
		}
		return conditions;
	}

	private Set<Condition<L, P>> getOrigConditions() {
		final Set<Condition<L, P>> conditions = new HashSet<>();
		for (final Condition<L, P> cond : mConditions) {
			if (mOriginalPlaces.contains(cond.getPlace())) {
				conditions.add(cond);
			}
		}
		return conditions;
	}

	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private static final class Statistics extends AbstractStatisticsDataProvider {
		public static final String OWICKI_GRIES_TIME = "EmpireToOwickiGries time";

		public static final String FEDERATION_VALIDITY_TIME = "Federation validity check time";
		public static final String OWICKI_GRIES_VALIDITY_TIME = "Owicki-Gries validity check time";

		public static final String FEDERATION_STATISTICS = "Federation statistics";

		private IStatisticsDataProvider mCrownStatistics;
		private IStatisticsDataProvider mFederationStatistics;

		private final TimeTracker mEmpireTime = new TimeTracker();
		private final TimeTracker mOwickiGriesTime = new TimeTracker();
		private final TimeTracker mFederationValidityTime = new TimeTracker();
		private final TimeTracker mOwickiGriesValidityTime = new TimeTracker();

		public Statistics() {
			declare(OWICKI_GRIES_TIME, () -> mOwickiGriesTime, KeyType.TT_TIMER_MS);
			declare(FEDERATION_VALIDITY_TIME, () -> mFederationValidityTime, KeyType.TT_TIMER_MS);
			declare(OWICKI_GRIES_VALIDITY_TIME, () -> mOwickiGriesValidityTime, KeyType.TT_TIMER_MS);

			// forward(CROWN_STATISTICS, () -> mCrownStatistics);
			forward(FEDERATION_STATISTICS, () -> mFederationStatistics);
		}

		private void reportFederationStatistics(final FederationComputation<?, ?> federationComp) {
			mFederationStatistics = federationComp.getStatistics();
		}

		private <T> T measureFederationValidity(final Supplier<T> runner) {
			return mFederationValidityTime.measure(runner);
		}

	}
}
