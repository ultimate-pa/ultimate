/*
 * Copyright (C) 2023 Matthias Zumkeller
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.IPossibleInterferences;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.PetriOwickiGriesValidityCheck;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.crown.Crown;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.crown.CrownConstruction;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.crown.CrownsEmpire;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.crown.PlacesCoRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.TimeTracker;

public class PetriOwickiGries<LETTER extends IAction, PLACE> {
	public static final boolean IGNORE_CUTOFF_CONDITIONS = true;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final BasicPredicateFactory mFactory;

	private final IIcfgSymbolTable mSymbolTable;
	private final Set<String> mProcedures;
	private final ModifiableGlobalsTable mModifiableGlobals;

	private final IPetriNet<LETTER, PLACE> mNet;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> mProduct;
	private final Function<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> mDiff2OriginalTransition;

	private final Set<PLACE> mOriginalPlaces;

	private final BranchingProcess<LETTER, PLACE> mBp;
	private final Set<Condition<LETTER, PLACE>> mConditions;
	private final Set<Condition<LETTER, PLACE>> mOriginalConditions;
	private final Set<Condition<LETTER, PLACE>> mAssertionConditions;

	private final Crown<PLACE, LETTER> mCrown;
	private final EmpireAnnotation<PLACE> mEmpireAnnotation;
	private final OwickiGriesAnnotation<Transition<LETTER, PLACE>, PLACE, Marking<PLACE>> mOwickiGriesAnnotation;

	private final Statistics mStatistics = new Statistics();

	public enum EmpireComputationMode {
		CROWNS, SYMBOLIC_EXECUTION
	}

	/**
	 *
	 * @param bp
	 *            finite prefix of unfolding for the refined net
	 * @param net
	 *            the original Petri program
	 */
	public PetriOwickiGries(final IUltimateServiceProvider services, final BranchingProcess<LETTER, PLACE> bp,
			final IPetriNet<LETTER, PLACE> net,
			final Function<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> diff2OriginalTransition,
			final BasicPredicateFactory factory, final Function<PLACE, IPredicate> placeToAssertion,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final ModifiableGlobalsTable modifiableGlobals,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> product,
			final EmpireComputationMode mode) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(PetriOwickiGries.class);
		mMgdScript = mgdScript;
		mFactory = factory;

		mSymbolTable = symbolTable;
		mProcedures = procedures;
		mModifiableGlobals = modifiableGlobals;

		mNet = net;
		mProduct = product;
		mOriginalPlaces = mNet.getPlaces();
		mDiff2OriginalTransition = diff2OriginalTransition;

		mBp = bp;
		mConditions = getConditions();
		mOriginalConditions = getOrigConditions();
		mAssertionConditions = DataStructureUtils.difference(mConditions, mOriginalConditions);

		mLogger.setLevel(LogLevel.INFO);

		final long cutoffs = bp.getConditions().stream().filter(c -> c.getPredecessorEvent().isCutoffEvent()).count();
		mLogger.info("""
				Constructing Owicki-Gries proof for Petri program that %s and unfolding that %s.\
				 %d conditions belong to cutoff events, %d conditions do not.\
				 %d conditions are original conditions, %d conditions are assertion conditions.""",
				net.sizeInformation(), bp.sizeInformation(), cutoffs, bp.getConditions().size() - cutoffs,
				mOriginalConditions.size(), mAssertionConditions.size());

		if (mode == EmpireComputationMode.CROWNS) {
			mCrown = getCrown();
			mLogger.debug("Constructed Crown:\n%s", mCrown);
			mEmpireAnnotation = getEmpireAnnotationFromCrown(placeToAssertion);
		} else {
			assert mode == EmpireComputationMode.SYMBOLIC_EXECUTION;
			mCrown = null;

			final var implicationChecker = new MonolithicImplicationChecker(services, mgdScript);
			final var htc = new MonolithicHoareTripleChecker(mgdScript, modifiableGlobals);
			final var computation = getEmpireComputation(implicationChecker, htc);
			mEmpireAnnotation = computation.getEmpire();
		}
		assert checkEmpireValidity() : "Empire annotation is invalid";

		mLogger.debug("Constructed Empire Annotation:\n%s", mEmpireAnnotation);
		mOwickiGriesAnnotation = getOwickiGriesAnnotation();
		mLogger.debug("Computed Owicki-Gries annotation:\n%s", mOwickiGriesAnnotation);
		mLogger.info("Owicki-Gries size: %s", mOwickiGriesAnnotation.size());
		assert checkOwickiGriesValidity() : "Owicki Gries annotation is invalid";
		mLogger.info("OG size: %s", mOwickiGriesAnnotation.size());
	}

	public static final boolean isCutoff(final Condition<?, ?> cond) {
		return cond.getPredecessorEvent().isCutoffEvent();
	}

	public static <LETTER, PLACE> IPossibleInterferences<Transition<LETTER, PLACE>, PLACE> getPossibleInterferences(
			final BranchingProcess<LETTER, PLACE> bp, final Set<PLACE> originalPlaces,
			final Function<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> diff2OriginalTransition) {
		final HashRelation<PLACE, Transition<LETTER, PLACE>> relation = new HashRelation<>();
		final ICoRelation<LETTER, PLACE> coRelation = bp.getCoRelation();

		for (final Condition<LETTER, PLACE> condition : bp.getConditions()) {
			final PLACE place = condition.getPlace();
			if (!originalPlaces.contains(place)) {
				continue;
			}
			for (final Event<LETTER, PLACE> event : coRelation.computeCoRelatatedEvents(condition)) {
				final Transition<LETTER, PLACE> transition = event.getTransition();
				if (!transition.getPredecessors().contains(place)) {
					final var originalTransition = diff2OriginalTransition.apply(transition);
					assert originalTransition != null : "no original transition for " + transition;
					relation.addPair(place, originalTransition);
				}
			}
		}
		return IPossibleInterferences.fromRelation(relation);
	}

	private Crown<PLACE, LETTER> getCrown() {
		final CrownConstruction<PLACE, LETTER> crownConstruction =
				new CrownConstruction<>(mServices, mBp, mOriginalConditions, mAssertionConditions);
		mStatistics.reportCrownStatistics(crownConstruction);
		mLogger.info("PetriOwickiGries Crown Statistics: %s", crownConstruction.getStatistics());
		return crownConstruction.getCrown();
	}

	private EmpireAnnotation<PLACE> getEmpireAnnotationFromCrown(final Function<PLACE, IPredicate> placeToAssertion) {
		final CrownsEmpire<PLACE, LETTER> crownsEmpire =
				mStatistics.measureEmpire(() -> mCrown.getCrownsEmpire(mFactory, placeToAssertion));
		mStatistics.reportEmpireStatistics(crownsEmpire);
		mLogger.info("PetriOwickiGries Empire Statistics: %s", crownsEmpire.getStatistics());
		return crownsEmpire.getEmpireAnnotation();
	}

	private EmpireComputation<LETTER, PLACE> getEmpireComputation(final MonolithicImplicationChecker implicationChecker,
			final MonolithicHoareTripleChecker mhc) {
		final var placesCorelation = new PlacesCoRelation<>(mBp);
		final var computation =
				new EmpireComputation<>(mServices, mFactory, mNet, placesCorelation, mProduct, mhc, implicationChecker);
		mStatistics.reportEmpireStatistics(computation);
		return computation;
	}

	private boolean checkEmpireValidity() {
		return mStatistics.measureEmpireValidity(() -> {
			final var implicationChecker = new MonolithicImplicationChecker(mServices, mMgdScript);
			final var checker = new EmpireValidityCheck<>(mServices, mMgdScript, implicationChecker, mFactory, mNet,
					mModifiableGlobals, mEmpireAnnotation);
			return checker.getValidity();
		}) != Validity.INVALID;
	}

	private OwickiGriesAnnotation<Transition<LETTER, PLACE>, PLACE, Marking<PLACE>> getOwickiGriesAnnotation() {
		final var annotation = mStatistics.measureOwickiGries(() -> {
			final var possibleInterferences = getPossibleInterferences(mBp, mOriginalPlaces, mDiff2OriginalTransition);
			final EmpireToOwickiGries<LETTER, PLACE> empireToOwickiGries = new EmpireToOwickiGries<>(mServices,
					mMgdScript, mNet, mSymbolTable, mProcedures, mEmpireAnnotation, possibleInterferences);
			return empireToOwickiGries.getAnnotation();
		});
		mLogger.info("Computed Owicki-Gries annotation with %d ghost variables, %d ghost updates, and overall size %d",
				annotation.getGhostVariables().size(), annotation.getAssignmentMapping().size(), annotation.size());
		return annotation;
	}

	private boolean checkOwickiGriesValidity() {
		return mStatistics.measureOwickiGriesValidity(() -> {
			final PetriOwickiGriesValidityCheck<LETTER, PLACE> owickiGriesValidity =
					new PetriOwickiGriesValidityCheck<>(mServices, mMgdScript, mNet, mModifiableGlobals,
							mOwickiGriesAnnotation);
			return owickiGriesValidity.isValid();
		}) != Validity.INVALID;
	}

	private Set<Condition<LETTER, PLACE>> getConditions() {
		Set<Condition<LETTER, PLACE>> conditions;
		if (IGNORE_CUTOFF_CONDITIONS) {
			mLogger.info("Ignoring conditions belonging to cutoff events.");
			conditions = mBp.getConditions().stream().filter(c -> !isCutoff(c)).collect(Collectors.toSet());
		} else {
			conditions = mBp.getConditions().stream().collect(Collectors.toSet());
		}
		return conditions;
	}

	private Set<Condition<LETTER, PLACE>> getOrigConditions() {
		final Set<Condition<LETTER, PLACE>> conditions = new HashSet<>();
		for (final Condition<LETTER, PLACE> cond : mConditions) {
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
		public static final String EMPIRE_TIME = "Crown empire time";
		public static final String OWICKI_GRIES_TIME = "EmpireToOwickiGries time";

		public static final String EMPIRE_VALIDITY_TIME = "Empire validity check time";
		public static final String OWICKI_GRIES_VALIDITY_TIME = "Owicki-Gries validity check time";

		public static final String CROWN_STATISTICS = "Crown construction";
		public static final String EMPIRE_STATISTICS = "Empire statistics";

		private IStatisticsDataProvider mCrownStatistics;
		private IStatisticsDataProvider mEmpireStatistics;

		private final TimeTracker mEmpireTime = new TimeTracker();
		private final TimeTracker mOwickiGriesTime = new TimeTracker();
		private final TimeTracker mEmpireValidityTime = new TimeTracker();
		private final TimeTracker mOwickiGriesValidityTime = new TimeTracker();

		public Statistics() {
			declareTimeTracker(EMPIRE_TIME, mEmpireTime);
			declareTimeTracker(OWICKI_GRIES_TIME, mOwickiGriesTime);
			declareTimeTracker(EMPIRE_VALIDITY_TIME, mEmpireValidityTime);
			declareTimeTracker(OWICKI_GRIES_VALIDITY_TIME, mOwickiGriesValidityTime);

			forward(CROWN_STATISTICS, () -> mCrownStatistics);
			forward(EMPIRE_STATISTICS, () -> mEmpireStatistics);
		}

		private void reportCrownStatistics(final CrownConstruction<?, ?> crownConstruction) {
			mCrownStatistics = crownConstruction.getStatistics();
		}

		private void reportEmpireStatistics(final EmpireComputation<?, ?> empireComp) {
			mEmpireStatistics = empireComp.getStatistics();
		}

		private void reportEmpireStatistics(final CrownsEmpire<?, ?> crownsEmpire) {
			mEmpireStatistics = crownsEmpire.getStatistics();
		}

		private <T> T measureEmpire(final Supplier<T> runner) {
			return mEmpireTime.measure(runner);
		}

		private <T> T measureOwickiGries(final Supplier<T> runner) {
			return mOwickiGriesTime.measure(runner);
		}

		private <T> T measureEmpireValidity(final Supplier<T> runner) {
			return mEmpireValidityTime.measure(runner);
		}

		private <T> T measureOwickiGriesValidity(final Supplier<T> runner) {
			return mOwickiGriesValidityTime.measure(runner);
		}
	}
}
