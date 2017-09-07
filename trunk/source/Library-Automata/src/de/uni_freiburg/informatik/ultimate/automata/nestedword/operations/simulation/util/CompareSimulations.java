/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationCheckResultStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSatDirect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed.BuchiReduce;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed.nwa.ReduceNwaDelayedSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct.MinimizeDfaSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct.nwa.ReduceNwaDirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble.ReduceNwaDelayedFullMultipebbleSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble.ReduceNwaDirectFullMultipebbleSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.ReduceNwaDelayedSimulationB;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.ReduceNwaDirectSimulationB;

/**
 * Compares different simulation methods.
 * <p>
 * Careful: The methods should use the same preprocessing to be comparable. They should also only be compared for finite
 * automata.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class CompareSimulations<LETTER, STATE>
		extends GeneralOperation<LETTER, STATE, IMinimizationCheckResultStateFactory<STATE>> {
	private final boolean mResult;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if some operation was canceled
	 */
	public CompareSimulations(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		super(services);

		final MinimizeDfaSimulation<LETTER, STATE> minimizeDfaSimulation =
				new MinimizeDfaSimulation<>(services, stateFactory, operand);
		final ReduceNwaDirectSimulation<LETTER, STATE> reduceNwaDirectSimulation =
				new ReduceNwaDirectSimulation<>(services, stateFactory, operand);
		final ReduceNwaDirectSimulationB<LETTER, STATE> reduceNwaDirectSimulationB =
				new ReduceNwaDirectSimulationB<>(services, stateFactory, operand);
		final ReduceNwaDirectFullMultipebbleSimulation<LETTER, STATE> reduceNwaDirectFullMultipebbleSimulation =
				new ReduceNwaDirectFullMultipebbleSimulation<>(services, stateFactory, operand);
		final MinimizeNwaPmaxSatDirect<LETTER, STATE> minimizeNwaPmaxSatAsymmetric =
				new MinimizeNwaPmaxSatDirect<>(services, stateFactory, operand);

		final BuchiReduce<LETTER, STATE> buchiReduce = new BuchiReduce<>(services, stateFactory, operand);
		final ReduceNwaDelayedSimulation<LETTER, STATE> reduceNwaDelayedSimulation =
				new ReduceNwaDelayedSimulation<>(services, stateFactory, operand);
		final ReduceNwaDelayedSimulationB<LETTER, STATE> reduceNwaDelayedSimulationB =
				new ReduceNwaDelayedSimulationB<>(services, stateFactory, operand);
		final ReduceNwaDelayedFullMultipebbleSimulation<LETTER, STATE> reduceNwaDelayedFullMultipebbleSimulation =
				new ReduceNwaDelayedFullMultipebbleSimulation<>(services, stateFactory, operand);

		final int directFin = minimizeDfaSimulation.getResult().size();
		final int direct1 = reduceNwaDirectSimulation.getResult().size();
		final int directB = reduceNwaDirectSimulationB.getResult().size();
		final int directF = reduceNwaDirectFullMultipebbleSimulation.getResult().size();
		final int directPmaxSat = minimizeNwaPmaxSatAsymmetric.getResult().size();

		final int delayedFin = buchiReduce.getResult().size();
		final int delayed1 = reduceNwaDelayedSimulation.getResult().size();
		final int delayedB = reduceNwaDelayedSimulationB.getResult().size();
		final int delayedF = reduceNwaDelayedFullMultipebbleSimulation.getResult().size();

		// we ignore direct1 and delayed1
		// @formatter:off
		mResult =
				directFin == directB
				&&
				directB == directF
				&&
				directB == directPmaxSat
				&&
				delayedFin == delayedB
				&&
				delayedB == delayedF
				;
		// @formatter:on

		mLogger.info(directFin + " MinimizeDfaSimulation");
		mLogger.info(direct1 + " (ReduceNwaDirectSimulation)");
		mLogger.info(directB + " ReduceNwaDirectSimulationB");
		mLogger.info(directF + " ReduceNwaDirectFullMultipebbleSimulation");
		mLogger.info(directPmaxSat + " MinimizeNwaPmaxSatAsymmetric");
		mLogger.info(delayedFin + " BuchiReduce");
		mLogger.info(delayed1 + " (ReduceNwaDelayedSimulation)");
		mLogger.info(delayedB + " ReduceNwaDelayedSimulationB");
		mLogger.info(delayedF + " ReduceNwaDelayedFullMultipebbleSimulation");
		mLogger.info(mResult);
	}

	@Override
	public Object getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IMinimizationCheckResultStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return mResult;
	}
}
