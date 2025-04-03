/*
 * Copyright (C) 2025 Matthias Zumkeller
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
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
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.Region;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.Territory;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.MinMaxMed;

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
		final var automatonStatisticsComputation = empireToOG.getAutomatonStatistics();
		final var empireStatistics = new EmpireAutomataStatistics();
		empireStatistics.reportEmpire(automatonStatisticsComputation);
		mStatistics.reportEmpire(empireStatistics);
		mOwickiGries = empireToOG.getAnnotation();
		mLogger.debug("Computed Owicki-Gries annotation:\n%s", mOwickiGries);

		assert checkOwickiGriesValidity(mOwickiGries) : "Owicki Gries annotation is invalid";

		return mOwickiGries;
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
		public static final String TERRITORY_COUNT = "number of territories";

		public static final String REGION_TERRITORY = "number of regions per territory";
		public static final String PLACES_PER_REGION = "number of places per region";

		private long mAutomatonSize;
		private long mUniquePairs;
		private long mLawSize;
		private long mAnnotationSize;
		private long mRegionCount;
		private long mNumberOfTerritories;

		private final MinMaxMed mRegionsPerTerritory = new MinMaxMed();
		private final MinMaxMed mPlacesPerRegion = new MinMaxMed();

		public EmpireAutomataStatistics() {
			declareCounter(AUTOMATON_SIZE, () -> mAutomatonSize);
			declareCounter(UNIQUE_PAIRS, () -> mUniquePairs);
			declareCounter(LAW_SIZE, () -> mLawSize);
			declareCounter(ANNOTATION_SIZE, () -> mAnnotationSize);
			declareCounter(REGION_COUNT, () -> mRegionCount);
			declareCounter(TERRITORY_COUNT, () -> mNumberOfTerritories);

			declareMinMaxMed(REGION_TERRITORY, mRegionsPerTerritory);
			declareMinMaxMed(PLACES_PER_REGION, mPlacesPerRegion);
		}

		public void reportEmpire(final ComputeAutomataStatistics<?, ?> statisticsComputation) {
			mRegionCount = statisticsComputation.getRegionCount();
			mAutomatonSize = statisticsComputation.getAutomatonSize();
			mUniquePairs = statisticsComputation.getUniquePairsSize();
			mLawSize = statisticsComputation.getLawSize();
			mAnnotationSize = statisticsComputation.getAnnotationSize();
			mNumberOfTerritories = statisticsComputation.getNumberOfTerritories();

			mRegionsPerTerritory.report(statisticsComputation.getTerritories(), Territory::size);
			mPlacesPerRegion.report(statisticsComputation.getRegions(), Region::size);
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
