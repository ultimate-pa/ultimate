/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.Reflected;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;

public class AutomataMinimizationStatisticsGenerator extends BaseStatisticsDataProvider {

	public static final String AutomataMinimizationTime = "AutomataMinimizationTime";
	public static final String MinimizatonAttempts = "MinimizatonAttempts";
	public static final String NontrivialMinimizations = "NontrivialMinimizations";
	public static final String StatesRemovedByMinimization = "StatesRemovedByMinimization";

	@Reflected(prettyName = AutomataMinimizationTime)
	@Statistics(type = DefaultMeasureDefinitions.LONG_TIME)
	private final long mAutomataMinimizationTime;

	@Reflected(prettyName = MinimizatonAttempts)
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private final int mMinimizatonAttempt;

	@Reflected(prettyName = NontrivialMinimizations)
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private final int mNontrivialMinimizaton;

	@Reflected(prettyName = StatesRemovedByMinimization)
	@Statistics(type = DefaultMeasureDefinitions.LONG_COUNTER)
	private final long mStatesRemovedByMinimization;

	public AutomataMinimizationStatisticsGenerator(final IToolchainStorage storage, final long automataMinimizationTime,
			final boolean minimizatonAttempt, final boolean nontrivialMinimizaton,
			final long statesRemovedByMinimization) {
		super(storage);
		mAutomataMinimizationTime = automataMinimizationTime;
		mMinimizatonAttempt = minimizatonAttempt ? 1 : 0;
		mNontrivialMinimizaton = nontrivialMinimizaton ? 1 : 0;
		mStatesRemovedByMinimization = statesRemovedByMinimization;
	}

}
