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
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import java.util.Objects;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.MinMaxMed;
import de.uni_freiburg.informatik.ultimate.util.statistics.TimeTracker;

abstract class OwickiGriesStatistics extends AbstractStatisticsDataProvider {
	public static final String EMPIRE_VALIDITY_TIME = "Empire validity check time";
	public static final String OWICKI_GRIES_VALIDITY_TIME = "Owicki-Gries validity check time";

	protected final ILogger mLogger;

	private final TimeTracker mEmpireTime = new TimeTracker();
	private IStatisticsDataProvider mEmpireStatistics;
	private final TimeTracker mEmpireValidityTime = new TimeTracker();

	private final TimeTracker mOwickiGriesTime = new TimeTracker();
	private final TimeTracker mOwickiGriesValidityTime = new TimeTracker();

	public OwickiGriesStatistics(final ILogger logger, final Class<?> empireComputation, final Class<?> ogComputation) {
		mLogger = logger;

		if (empireComputation != null) {
			declareTimeTracker(empireComputation.getSimpleName() + " time", mEmpireTime);
			forward(empireComputation.getSimpleName() + " statistics", () -> mEmpireStatistics);
			declareTimeTracker(EMPIRE_VALIDITY_TIME, mEmpireValidityTime);
		}

		Objects.requireNonNull(ogComputation);
		declareTimeTracker(ogComputation.getSimpleName() + " time", mOwickiGriesTime);
		declareTimeTracker(OWICKI_GRIES_VALIDITY_TIME, mOwickiGriesValidityTime);
	}

	// EMPIRES
	// ----------------------------

	public void startEmpireComputation() {
		mEmpireTime.start();
	}

	public void stopEmpireComputation() {
		mEmpireTime.stop();
	}

	public void reportEmpireStatistics(final IStatisticsDataProvider empireStatistics) {
		mEmpireStatistics = empireStatistics;

		// TODO measure size etc
		// TODO log information
	}

	public void startEmpireValidity() {
		mEmpireValidityTime.start();
	}

	public void stopEmpireValidity() {
		mEmpireValidityTime.stop();
	}

	// OWICKI-GRIES
	// ----------------------------

	public void startOwickiGriesComputation() {
		mOwickiGriesTime.start();
	}

	public void stopOwickiGriesComputation() {
		mOwickiGriesTime.stop();
	}

	public void reportOwickiGries(final OwickiGriesAnnotation<?, ?, ?> annotation) {
		// TODO measure size etc
		// TODO log information
		mLogger.info("Computed Owicki-Gries annotation with %d ghost variables, %d ghost updates, and overall size %d",
				annotation.getGhostVariables().size(), annotation.getGhostUpdateMap().size(), annotation.size());
		printModularityData(mLogger, annotation);
	}

	public void startOwickiGriesValidity() {
		mOwickiGriesValidityTime.start();
	}

	public void stopOwickiGriesValidity() {
		mOwickiGriesValidityTime.stop();
	}

	// TODO temporary; integrate this into the regular statistics
	public static void printModularityData(final ILogger logger, final OwickiGriesAnnotation<?, ?, ?> annotation) {
		final MinMaxMed freeVars = new MinMaxMed();
		freeVars.report(annotation.getAnnotationMap().values(), fm -> fm.getFormula().getFreeVars().length);
		logger.info("free variables mentioned in invariants: " + freeVars);

		final MinMaxMed ghostVars = new MinMaxMed();
		ghostVars.report(annotation.getAnnotationMap().values(),
				fm -> fm.getVars().stream().filter(annotation.getGhostVariables()::contains).count());
		logger.info("ghost variables mentioned in invariants: " + ghostVars);

		final MinMaxMed programVars = new MinMaxMed();
		programVars.report(annotation.getAnnotationMap().values(),
				fm -> fm.getVars().stream().filter(Predicate.not(annotation.getGhostVariables()::contains)).count());
		logger.info("program variables mentioned in invariants: " + programVars);
	}
}
