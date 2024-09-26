/*
 * Copyright (C) 2024 Marcel Ebbinghaus
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IConditionalCommutativityCheckerStatisticsUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.ConditionalCommutativityStatisticsGenerator.ConditionalCommutativityStatisticsDefinitions;

// TODO decouple statistics from CegarLoopStatisticsGenerator!
// The classes for conditional commutativity should collect their own statistics,
// which may in the end be added to the CEGAR loop's statistics.
/**
 * Implementation of {@link IConditionalCommutativityCheckerStatisticsUtils} which is responsible for managing any
 * statistics regarding conditional commutativity checks.
 * 
 * @author Marcel Ebbinghaus
 *
 */
public class ConditionalCommutativityCheckerStatisticsUtils implements IConditionalCommutativityCheckerStatisticsUtils {

	private final ConditionalCommutativityStatisticsGenerator mGenerator;

	public ConditionalCommutativityCheckerStatisticsUtils(final ConditionalCommutativityStatisticsGenerator generator) {
		mGenerator = generator;
	}

	@Override
	public void startStopwatch() {
		mGenerator.start(ConditionalCommutativityStatisticsDefinitions.ConditionalCommutativityCheckTime);
	}

	@Override
	public void stopStopwatch() {
		mGenerator.stop(ConditionalCommutativityStatisticsDefinitions.ConditionalCommutativityCheckTime);
	}

	@Override
	public void addDFSRestart() {
		mGenerator.addConditionalCommutativityDFSRestart();
	}

	@Override
	public void addIAIntegration() {
		mGenerator.addConditionalCommutativityIAIntegration();
	}

	@Override
	public void addConditionCalculation() {
		mGenerator.addConditionalCommutativityConditionCalculation();
	}

	@Override
	public void addTraceCheck() {
		mGenerator.addConditionalCommutativityTraceCheck();
	}

	@Override
	public void addImperfectProof() {
		mGenerator.addConditionalCommutativityImperfectProof();
	}
}
