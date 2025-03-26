package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.UnionNwa;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IUnionStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.ComputeAutomataStatistics;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomatonToOG;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomatonValidityCheck;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireComputation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireToOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.PetriOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;

public class EmpireAutomataOwickiGries<L extends IAction, P> implements IPetriNetProofProducer<L, P> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IPetriNet<L, P> mProgram;
	private final ManagedScript mMgdScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final Set<String> mProcedures;
	private final ModifiableGlobalsTable mModifiableGlobals;
	private final BasicPredicateFactory mFactory;
	private BranchingProcess<L, P> mRefinedUnfolding;

	private final IUnionStateFactory<IPredicate> mUnionFactory;
	private final Statistics mStatistics;

	private Function<Transition<L, P>, Transition<L, P>> mDiff2OriginalTransition = Function.identity();
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mProofProduct;
	private OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> mOwickiGries;

	public EmpireAutomataOwickiGries(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final CfgSmtToolkit csToolkit, final PredicateFactory factory) {
		this(services, program, csToolkit.getManagedScript(), csToolkit.getSymbolTable(), csToolkit.getProcedures(),
				csToolkit.getModifiableGlobalsTable(), factory);
	}

	public EmpireAutomataOwickiGries(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final ModifiableGlobalsTable modifiableGlobals, final PredicateFactory factory) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		mProgram = program;
		mMgdScript = mgdScript;
		mSymbolTable = symbolTable;
		mProcedures = procedures;
		mModifiableGlobals = modifiableGlobals;
		mFactory = factory;
		mUnionFactory = new UnionFactory(factory);
		mStatistics = new Statistics(mLogger);
	}

	@Override
	public void refine(final IPredicateUnifier unifier, final INestedWordAutomaton<L, IPredicate> interpolantAutomaton,
			final Map<Transition<L, P>, Transition<L, P>> transitionBacktranslation) {
		mDiff2OriginalTransition = mDiff2OriginalTransition.compose(transitionBacktranslation::get);
		if (mProofProduct == null) {
			mProofProduct = interpolantAutomaton;
		} else {
			final var initialTrueState1 =
					DataStructureUtils.getOneAndOnly(mProofProduct.getInitialStates(), "initial state");
			final var totalizedProduct = new TotalizeNwa<>(mProofProduct, initialTrueState1, false);

			final var initialTrueState2 =
					DataStructureUtils.getOneAndOnly(interpolantAutomaton.getInitialStates(), "initial state");
			final var totalizedProof = new TotalizeNwa<>(interpolantAutomaton, initialTrueState2, false);

			try {
				mProofProduct = new UnionNwa<>(totalizedProduct, totalizedProof, mUnionFactory, false);
			} catch (final AutomataLibraryException e) {
				throw new AssertionError(e);
			}
		}
	}

	@Override
	public boolean isReadyToComputeProof() {
		return true;
	}

	@Override
	public OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> getOrComputeProof() {
		mStatistics.startEmpireComputation();
		final var automaton = new EmpireAutomaton<>(mProgram, mProofProduct, mServices);
		mStatistics.stopEmpireComputation();
		mLogger.debug("Constructed Empire Automaton");

		assert checkAutomatonValidity(automaton) : "Empire automaton is invalid";

		final var empireToOG = getOwickiGriesAnnotation(automaton);
		final var automatonStatisticsComputation = getAutomataStatisticsComputation(empireToOG);
		final var empireStatistics = new EmpireAutomataStatistics();
		empireStatistics.reportEmpire(automatonStatisticsComputation);
		mStatistics.reportEmpire(empireStatistics);
		mOwickiGries = empireToOG.getAnnotation();
		mLogger.debug("Computed Owicki-Gries annotation:\n%s", mOwickiGries);

		assert checkOwickiGriesValidity(mOwickiGries) : "Owicki Gries annotation is invalid";

		return mOwickiGries;
	}

	private ComputeAutomataStatistics<L, P>
			getAutomataStatisticsComputation(final EmpireAutomatonToOG<L, P> empireAutomatonToOG) {
		final var automaton = empireAutomatonToOG.getAutomatonReachableStates();
		return new ComputeAutomataStatistics<>(automaton);
	}

	private boolean checkAutomatonValidity(final EmpireAutomaton<L, P> automaton) {
		mStatistics.startEmpireValidity();
		try {
			final var checker = new EmpireAutomatonValidityCheck<>(mServices, mMgdScript, mFactory, mProgram,
					mModifiableGlobals, automaton);
			return checker.getValidity() != Validity.INVALID;
		} finally {
			mStatistics.stopEmpireValidity();
		}
	}

	private boolean checkOwickiGriesValidity(final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> annotation) {
		mStatistics.startOwickiGriesValidity();
		try {
			final var validity =
					new PetriOwickiGriesValidityCheck<>(mServices, mMgdScript, mProgram, mModifiableGlobals, annotation)
							.isValid();
			assert validity != Validity.INVALID : "Owicki-Gries annotation is invalid";
			if (validity == Validity.UNKNOWN) {
				mLogger.warn("Could not prove validity of Owicki-Gries annotation");
			}
			return validity != Validity.INVALID;
		} finally {
			mStatistics.stopOwickiGriesValidity();
		}
	}

	@Override
	public void finalize(final IPetriNet<L, P> refinedNet, final BranchingProcess<L, P> refinedNetUnfolding) {
		mRefinedUnfolding = refinedNetUnfolding;
	}

	@Override
	public IPetriNet<L, P> getProgram() {
		return mProgram;
	}

	private EmpireAutomatonToOG<L, P> getOwickiGriesAnnotation(final EmpireAutomaton<L, P> empireAutomaton) {
		mStatistics.startOwickiGriesComputation();
		final var possibleInterferences = PetriOwickiGries.getPossibleInterferences(mRefinedUnfolding,
				mProgram.getPlaces(), mDiff2OriginalTransition);
		final EmpireAutomatonToOG<L, P> empireToOwickiGries = new EmpireAutomatonToOG<>(mServices, mMgdScript, mProgram,
				mSymbolTable, mProcedures, empireAutomaton, possibleInterferences);
		mStatistics.stopOwickiGriesComputation();
		return empireToOwickiGries;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private static final class Statistics extends OwickiGriesStatistics {
		public Statistics(final ILogger logger) {
			super(logger, EmpireComputation.class, EmpireToOwickiGries.class);
		}

		public void reportEmpire(final IStatisticsDataProvider statistics) {
			reportEmpireStatistics(statistics, null);
		}
	}

	public static final class EmpireAutomataStatistics extends AbstractStatisticsDataProvider {
		public static final String AUTOMATON_SIZE = "automaton size";
		public static final String UNIQUE_PAIRS = "number of unique pairs";
		public static final String LAW_SIZE = "empire law size";
		public static final String ANNOTATION_SIZE = "empire annotation size";
		public static final String REGION_COUNT = "number of regions";

		public static final String REGION_TERRITORY = "number of regions per territory";
		public static final String PLACES_PER_REGION = "number of places per region";

		private long mAutomatonSize;
		private long mUniquePairs;
		private long mLawSize;
		private long mAnnotationSize;
		private long mRegionCount;

		public EmpireAutomataStatistics() {
			declare(AUTOMATON_SIZE, () -> mAutomatonSize, KeyType.COUNTER);
			declare(UNIQUE_PAIRS, () -> mUniquePairs, KeyType.COUNTER);
			declare(LAW_SIZE, () -> mLawSize, KeyType.COUNTER);
			declare(ANNOTATION_SIZE, () -> mAnnotationSize, KeyType.COUNTER);
			declare(REGION_COUNT, () -> mRegionCount, KeyType.COUNTER);
		}

		public void reportEmpire(final ComputeAutomataStatistics<?, ?> statisticsComputation) {
			mRegionCount = statisticsComputation.getRegionCount();
			mAutomatonSize = statisticsComputation.getAutomatonSize();
			mUniquePairs = statisticsComputation.getUniquePairsSize();
			mLawSize = statisticsComputation.getLawSize();
			mAnnotationSize = statisticsComputation.getAnnotationSize();
		}
	}

	private static final class UnionFactory implements IUnionStateFactory<IPredicate> {
		private final PredicateFactory mPredicateFactory;
		private final IPredicate mEmptyStack;

		public UnionFactory(final PredicateFactory predicateFactory) {
			mPredicateFactory = predicateFactory;
			mEmptyStack = predicateFactory.newEmptyStackPredicate();
		}

		@Override
		public IPredicate createEmptyStackState() {
			return mEmptyStack;
		}

		@Override
		public IPredicate createSinkStateContent() {
			return mPredicateFactory.and();
		}

		@Override
		public IPredicate union(final IPredicate state1, final IPredicate state2) {
			return mPredicateFactory.and(state1, state2);
		}
	}
}
