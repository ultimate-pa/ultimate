/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automata Library, or any covered work, by linking or combining it
 * with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE Automata Library grant you additional permission to convey the
 * resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;

/**
 * Minimization of nested word automata which chooses the actual minimization operation based on the size of the
 * automaton.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class MinimizeNwaMulti<LETTER, STATE> extends MinimizeNwaCombinator<LETTER, STATE> {
	/**
	 * Strategy to choose the minimization operation.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum Strategy {
		/**
		 * Default strategy.
		 */
		DEFAULT,
		/**
		 * Simulation-based strategy.
		 */
		SIMULATION_BASED
	}

	private static final int DEFAULT_MINIMIZE_MAX_SAT_SIZE = 10_000;

	private static final int SIMULATION_BASED_DIRECT_SIZE = 2_000;

	/**
	 * Constructor with default strategy.
	 * 
	 * @param services
	 *            services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input automaton
	 * @param partition
	 *            pre-defined partition of states
	 * @param addMapOldState2newState
	 *            add map old state 2 new state?
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public MinimizeNwaMulti(final AutomataLibraryServices services, final IMinimizationStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand, final ISetOfPairs<STATE, ?> partition,
			final boolean addMapOldState2newState) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, partition, addMapOldState2newState, Strategy.DEFAULT);
	}

	/**
	 * Constructor with given strategy.
	 * 
	 * @param services
	 *            services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input automaton
	 * @param partition
	 *            pre-defined partition of states
	 * @param addMapOldState2newState
	 *            add map old state 2 new state?
	 * @param strategy
	 *            strategy
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public MinimizeNwaMulti(final AutomataLibraryServices services, final IMinimizationStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand, final ISetOfPairs<STATE, ?> partition,
			final boolean addMapOldState2newState, final Strategy strategy) throws AutomataOperationCanceledException {
		super(services, stateFactory, operand);
		mMode = chooseMinimization(operand, strategy);
		super.run(partition, addMapOldState2newState);
	}

	private MinimizationMethods chooseMinimization(final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final Strategy strategy) {
		switch (strategy) {
			case DEFAULT:
				return chooseDefaultMinimization(operand);
			case SIMULATION_BASED:
				return chooseSimulationBasedMinimization(operand);
			default:
				throw new IllegalArgumentException(UNDEFINED_ENUM_STATE_MESSAGE);
		}
	}

	/**
	 * Default strategy.
	 */
	private MinimizationMethods chooseDefaultMinimization(final IDoubleDeckerAutomaton<LETTER, STATE> operand) {
		if (operand.size() <= DEFAULT_MINIMIZE_MAX_SAT_SIZE) {
			// use MaxSat-based minimization up to certain limit
			return MinimizationMethods.NWA_MAX_SAT2;
		}
		// use no minimization for bigger automata
		return MinimizationMethods.NONE;
	}

	/**
	 * Simulation-based strategy.
	 */
	private MinimizationMethods chooseSimulationBasedMinimization(final IDoubleDeckerAutomaton<LETTER, STATE> operand) {
		if (operand.size() <= SIMULATION_BASED_DIRECT_SIZE) {
			// use direct simulation-based minimization up to certain limit
			return MinimizationMethods.NWA_RAQ_DIRECT;
		}
		// use no minimization for bigger automata
		return MinimizationMethods.NONE;
	}
}
