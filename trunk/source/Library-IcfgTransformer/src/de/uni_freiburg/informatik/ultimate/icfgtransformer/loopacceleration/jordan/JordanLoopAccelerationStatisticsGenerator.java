/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;

public class JordanLoopAccelerationStatisticsGenerator extends BaseStatisticsDataProvider {

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private final int mHavocedVariables;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private final int mAssignedVariables;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private final int mReadonlyVariables;

	// TODO: This was already a nested map with type int_counter before, how did this work?
	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private final NestedMap2<Integer, Integer, Integer> mEigenvalues;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mSequentialAcceleration;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mAlternatingAcceleration;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mQuantifierFreeResult;

	public JordanLoopAccelerationStatisticsGenerator(final IToolchainStorage storage,
			final int numberOfAssignedVariables, final int numberOfHavocedVariables,
			final int numberOfReadonlyVariables, final NestedMap2<Integer, Integer, Integer> eigenvalues) {
		super(storage);
		mAssignedVariables = numberOfAssignedVariables;
		mHavocedVariables = numberOfHavocedVariables;
		mReadonlyVariables = numberOfReadonlyVariables;
		mEigenvalues = eigenvalues;
		mSequentialAcceleration = 0;
		mQuantifierFreeResult = 0;
		mAlternatingAcceleration = 0;
	}

	public void reportSequentialAcceleration() {
		mSequentialAcceleration++;
	}

	public void reportAlternatingAcceleration() {
		mAlternatingAcceleration++;
	}

	public void reportQuantifierFreeResult() {
		mQuantifierFreeResult++;
	}
}
