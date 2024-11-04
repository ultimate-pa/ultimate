/*
 * Copyright (C) 2024 Marcel Ebbinghaus
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.conditional;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.conditional.ConditionalCommutativityStatisticsGenerator.ConditionalCommutativityStatisticsDefinitions;

/**
 * Responsible for managing any statistics regarding conditional commutativity checks.
 *
 * @author Marcel Ebbinghaus
 *
 */
public class ConditionalCommutativityCheckerStatisticsUtils {

	public enum ConditionalCommutativityStopwatches {
		CHECKER, CONDITION
	}

	private final ConditionalCommutativityStatisticsGenerator mGenerator;

	public ConditionalCommutativityCheckerStatisticsUtils(final ConditionalCommutativityStatisticsGenerator generator) {
		mGenerator = generator;
	}

	public void startStopwatch(final ConditionalCommutativityStopwatches stopwatch) {
		switch (stopwatch) {
		case CHECKER:
			mGenerator.start(ConditionalCommutativityStatisticsDefinitions.ConditionalCommutativityCheckTime);
			break;
		case CONDITION:
			mGenerator.start(
					ConditionalCommutativityStatisticsDefinitions.ConditionalCommutativityConditionCalculationTime);
			break;
		default:
			throw new AssertionError("unknown stopwatch");
		}
	}

	public void stopStopwatch(final ConditionalCommutativityStopwatches stopwatch) {
		switch (stopwatch) {
		case CHECKER:
			mGenerator.stop(ConditionalCommutativityStatisticsDefinitions.ConditionalCommutativityCheckTime);
			break;
		case CONDITION:
			mGenerator.stop(
					ConditionalCommutativityStatisticsDefinitions.ConditionalCommutativityConditionCalculationTime);
			break;
		default:
			throw new AssertionError("unknown stopwatch");
		}
	}

	public void addDFSRestart() {
		mGenerator.addConditionalCommutativityDFSRestart();
	}

	public void addIAIntegration() {
		mGenerator.addConditionalCommutativityIAIntegration();
	}

	public void addConditionCalculation() {
		mGenerator.addConditionalCommutativityConditionCalculation();
	}

	public void addTraceCheck() {
		mGenerator.addConditionalCommutativityTraceCheck();
	}

	public void addUnknownTraceCheck() {
		mGenerator.addConditionalCommutativityUnknownTraceCheck();
	}

	public void addImperfectProof() {
		mGenerator.addConditionalCommutativityImperfectProof();
	}

	public void addCommutingCounterexample() {
		mGenerator.addConditionalCommutativityCommutingCounterexample();

	}

	public void addQuantifiedCondition() {
		mGenerator.addConditionalCommutativityQuantifiedCondition();
	}

	public void addFalseCondition() {
		mGenerator.addConditionalCommutativityFalseCondition();
	}
}
