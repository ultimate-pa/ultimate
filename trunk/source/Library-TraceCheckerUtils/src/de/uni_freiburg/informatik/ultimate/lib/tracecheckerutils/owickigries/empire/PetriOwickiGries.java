/*
 * Copyright (C) 2023 Matthias Zumkeller
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
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
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.Crown;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.CrownConstruction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.CrownsEmpire;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;
import de.uni_freiburg.informatik.ultimate.util.statistics.TimeTracker;

public class PetriOwickiGries<LETTER extends IAction, PLACE> {

	private final ILogger mLogger;

	private final BranchingProcess<LETTER, PLACE> mBp;
	private final Set<Condition<LETTER, PLACE>> mConditions;
	private final Set<Condition<LETTER, PLACE>> mOriginalConditions;
	private final Set<Condition<LETTER, PLACE>> mAssertionConditions;
	private final Set<PLACE> mOriginalPlaces;
	private final IPetriNet<LETTER, PLACE> mNet;
	private final Crown<PLACE, LETTER> mCrown;
	private final EmpireAnnotation<PLACE> mEmpireAnnotation;

	private final Statistics mStatistics = new Statistics();

	/**
	 *
	 * @param bp
	 *            finite prefix of unfolding for the refined net
	 * @param net
	 *            the original Petri program
	 */
	public PetriOwickiGries(final IUltimateServiceProvider services, final BranchingProcess<LETTER, PLACE> bp,
			final IPetriNet<LETTER, PLACE> net, final BasicPredicateFactory factory,
			final Function<PLACE, IPredicate> placeToAssertion, final MonolithicImplicationChecker implicationChecker,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final ModifiableGlobalsTable modifiableGlobals) {
		mLogger = services.getLoggingService().getLogger(PetriOwickiGries.class);

		mBp = bp;
		mNet = net;
		mLogger.info("Constructing Owicki-Gries proof for Petri program that %s and unfolding that %s",
				net.sizeInformation(), bp.sizeInformation());

		mOriginalPlaces = mNet.getPlaces();
		mConditions = mBp.getConditions().stream().collect(Collectors.toSet());
		mOriginalConditions = getOrigConditions();
		mAssertionConditions = DataStructureUtils.difference(mConditions, mOriginalConditions);
		mCrown = getCrown();
		mEmpireAnnotation = getEmpireAnnotation(factory, placeToAssertion);
		final MarkingLaw<PLACE> markingLaw = new MarkingLaw<>(mEmpireAnnotation.getLaw(), factory);

		mStatistics.measureEmpireValidity(() -> {
			try {
				final var checker = new EmpireValidityCheck<>(markingLaw, net, factory, implicationChecker, services,
						mgdScript, symbolTable, modifiableGlobals);
				assert checker.getValidity() != Validity.INVALID : "Empire annotation is not valid";
			} catch (final PetriNetNot1SafeException e) {
				throw new IllegalArgumentException("Petri program must be 1-safe", e);
			}
		});
		final String empireString = mEmpireAnnotation.toString();
		final EmpireToOwickiGries<LETTER, PLACE> empireToOwickiGries = new EmpireToOwickiGries<>(mEmpireAnnotation,
				mgdScript, services, mLogger, symbolTable, procedures, mNet);
		mLogger.info("Constructed Empire Annotation: %s", empireString);
	}

	private Crown<PLACE, LETTER> getCrown() {
		final CrownConstruction<PLACE, LETTER> crownConstruction =
				new CrownConstruction<>(mBp, mOriginalConditions, mAssertionConditions, mNet);
		mStatistics.reportCrownStatistics(crownConstruction);
		mLogger.info("PetriOwickiGries Crown Statistics: %s", crownConstruction.getStatistics());
		return crownConstruction.getCrown();
	}

	private EmpireAnnotation<PLACE> getEmpireAnnotation(final BasicPredicateFactory factory,
			final Function<PLACE, IPredicate> placeToAssertion) {
		final CrownsEmpire<PLACE, LETTER> crownsEmpire = mStatistics.measureEmpire(() -> {
			final CrownsEmpire<PLACE, LETTER> empireConstruction = mCrown.getCrownsEmpire(factory, placeToAssertion);
			return empireConstruction;
		});
		mStatistics.reportEmpireStatistics(crownsEmpire);
		mLogger.info("PetriOwickiGries Empire Statistics: %s", crownsEmpire.getStatistics());
		return crownsEmpire.getEmpireAnnotation();
	}

	private Set<Condition<LETTER, PLACE>> getOrigConditions() {
		final Set<Condition<LETTER, PLACE>> conditions = new HashSet<>();
		for (final Condition<LETTER, PLACE> cond : mBp.getConditions()) {
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
		public static final String CROWN_STATISTICS = "Crown construction";
		public static final String EMPIRE_TIME = "Crown empire time";
		public static final String EMPIRE_VALIDITY_TIME = "Empire validity check time";
		public static final String EMPIRE_STATISTICS = "Empire statistics";

		private IStatisticsDataProvider mCrownStatistics;
		private final TimeTracker mEmpireTime = new TimeTracker();
		private final TimeTracker mEmpireValidityTime = new TimeTracker();
		private IStatisticsDataProvider mEmpireStatistics;

		public Statistics() {
			declare(EMPIRE_TIME, () -> mEmpireTime, KeyType.TT_TIMER_MS);
			declare(EMPIRE_VALIDITY_TIME, () -> mEmpireValidityTime, KeyType.TT_TIMER_MS);
			forward(CROWN_STATISTICS, () -> mCrownStatistics);
			forward(EMPIRE_STATISTICS, () -> mEmpireStatistics);
		}

		private void reportCrownStatistics(final CrownConstruction<?, ?> crownConstruction) {
			mCrownStatistics = crownConstruction.getStatistics();
		}

		private void reportEmpireStatistics(final CrownsEmpire<?, ?> crownsEmpire) {
			mEmpireStatistics = crownsEmpire.getStatistics();
		}

		private <T> T measureEmpire(final Supplier<T> runner) {
			return mEmpireTime.measure(runner);
		}

		private void measureEmpireValidity(final Runnable runner) {
			mEmpireValidityTime.measure(runner);
		}
	}
}
