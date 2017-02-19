/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed.nwa;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.LookaheadPartitionConstructor;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed.BuchiReduce;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementFkvStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs;

/**
 * Operation that reduces a given nwa automaton by using
 * {@link DelayedNwaSimulation}.<br/>
 * Once constructed the reduction automatically starts, the result can be get by
 * using {@link #getResult()}.<br/>
 * <br/>
 * For correctness its important that the inputed automaton has <b>no dead
 * ends</b> nor <b>duplicate transitions</b>.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class ReduceNwaDelayedSimulation<LETTER, STATE> extends BuchiReduce<LETTER, STATE> {
	
	/**
	 * Creates a new nwa reduce object that starts reducing the given nwa
	 * automaton.<br/>
	 * Once finished the result can be get by using {@link #getResult()}.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            The nwa to reduce
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public <FACTORY extends IMergeStateFactory<STATE> & IEmptyStackStateFactory<STATE>> ReduceNwaDelayedSimulation(
			final AutomataLibraryServices services,
			final FACTORY stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, false);
	}
	
	/**
	 * Creates a new nwa reduce object that starts reducing the given nwa
	 * automaton.<br/>
	 * Once finished the result can be get by using {@link #getResult()}.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            The nwa to reduce
	 * @param useSCCs
	 *            If the simulation calculation should be optimized using SCC,
	 *            Strongly Connected Components.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public <FACTORY extends IMergeStateFactory<STATE> & IEmptyStackStateFactory<STATE>> ReduceNwaDelayedSimulation(
			final AutomataLibraryServices services,
			final FACTORY stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final boolean useSCCs) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, useSCCs,
				new LookaheadPartitionConstructor<>(services, operand, true).getPartition());
	}
	
	/**
	 * Creates a new nwa reduce object that starts reducing the given nwa
	 * automaton.<br/>
	 * Once finished the result can be get by using {@link #getResult()}.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            The nwa to reduce
	 * @param useSCCs
	 *            If the simulation calculation should be optimized using SCC,
	 *            Strongly Connected Components.
	 * @param possibleEquivalenceClasses
	 *            A collection of sets which contains states of an automaton
	 *            that may be merge-able. States which are not in the same set
	 *            are definitely not merge-able which is used as an optimization
	 *            for the game graph
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public <FACTORY extends IMergeStateFactory<STATE> & IEmptyStackStateFactory<STATE>> ReduceNwaDelayedSimulation(
			final AutomataLibraryServices services,
			final FACTORY stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final boolean useSCCs, final PartitionBackedSetOfPairs<STATE> possibleEquivalenceClasses)
			throws AutomataOperationCanceledException {
		super(services, stateFactory, operand,
				new DelayedNwaSimulation<>(services.getProgressAwareTimer(),
						services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID), useSCCs, stateFactory,
						new DelayedNwaGameGraph<>(services, stateFactory,
								services.getProgressAwareTimer(),
								services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID),
								operand, possibleEquivalenceClasses.getRelation())));
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.
	 * simulation.delayed.BuchiReduce#checkResult(de.uni_freiburg.informatik.
	 * ultimate.automata.statefactory.IStateFactory)
	 */
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		getLogger().info("Start testing correctness of " + operationName());
		// TODO Christian 2017-02-10 Temporary workaround until state factory becomes class parameter
		final boolean correct = (new BuchiIsEquivalent<>(getServices(),
				(IBuchiComplementFkvStateFactory<STATE> & IDeterminizeStateFactory<STATE> & IBuchiIntersectStateFactory<STATE>) stateFactory,
				getOperand(), getResult())).getResult();
		getLogger().info("Finished testing correctness of " + operationName());
		return correct;
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.delayed.BuchiReduce#operationName()
	 */
	@Override
	public String operationName() {
		return "reduceNwaDelayedSimulation";
	}
}
