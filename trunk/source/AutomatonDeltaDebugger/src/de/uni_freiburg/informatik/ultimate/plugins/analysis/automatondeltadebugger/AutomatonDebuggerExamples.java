/*
 * Copyright (C) 2015-2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automaton Delta Debugger.
 * 
 * The ULTIMATE Automaton Delta Debugger is free software: you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * The ULTIMATE Automaton Delta Debugger is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automaton Delta Debugger. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automaton Delta Debugger, or any covered work, by linking or
 * combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automaton Delta Debugger grant you additional
 * permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaMaxSat2;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.ShrinkNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.arrays.MinimizeNwaMaxSAT;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed.BuchiReduce;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed.nwa.ReduceNwaDelayedSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct.nwa.ReduceNwaDirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * Examples used by delta debugger.
 * NOTE: Users may insert their sample code as a new method and leave it here.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
@SuppressWarnings("squid:S00112")
public class AutomatonDebuggerExamples<LETTER, STATE> {
	private final AutomataLibraryServices mServices;
	
	/**
	 * @param services
	 *            Ultimate services
	 */
	public AutomatonDebuggerExamples(final IUltimateServiceProvider services) {
		mServices = new AutomataLibraryServices(services);
	}
	
	/**
	 * implemented operations for quick usage
	 * NOTE: If another operation is supported, add a value here.
	 */
	public enum EOperationType {
		MINIMIZE_NWA_MAXSAT,
		MINIMIZE_NWA_MAXSAT2,
		REDUCE_NWA_DIRECT_SIMULATION,
		REDUCE_NWA_DELAYED_SIMULATION,
		SHRINK_NWA,
		BUCHI_REDUCE
	}
	
	/**
	 * @param type
	 *            operation type
	 * @param automaton
	 *            nested word automaton
	 * @param factory
	 *            state factory
	 * @return operation corresponding to type
	 * @throws Throwable
	 *             when operation fails
	 */
	public IOperation<LETTER, STATE> getOperation(final EOperationType type,
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final IStateFactory<STATE> factory) throws Throwable {
		switch (type) {
			case MINIMIZE_NWA_MAXSAT:
				return minimizeNwaMaxSAT(automaton, factory);
				
			case MINIMIZE_NWA_MAXSAT2:
				return minimizeNwaMaxSAT2(automaton, factory);
				
			case REDUCE_NWA_DIRECT_SIMULATION:
				return reduceNwaDirectSimulation(automaton, factory);
				
			case REDUCE_NWA_DELAYED_SIMULATION:
				return reduceNwaDelayedSimulation(automaton, factory);
				
			case SHRINK_NWA:
				return shrinkNwa(automaton, factory);
				
			case BUCHI_REDUCE:
				return buchiReduce(automaton, factory);
				
			default:
				throw new IllegalArgumentException("Unknown operation.");
		}
	}
	
	/**
	 * @param automaton
	 *            automaton
	 * @param factory
	 *            state factory
	 * @return new <code>MinimizeNwaMaxSAT()</code> instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<LETTER, STATE> minimizeNwaMaxSAT(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final IStateFactory<STATE> factory) throws Throwable {
		final IDoubleDeckerAutomaton<LETTER, STATE> preprocessed =
				new RemoveUnreachable<LETTER, STATE>(mServices, automaton).getResult();
		return new MinimizeNwaMaxSAT<LETTER, STATE>(mServices, factory, preprocessed);
	}
	
	/**
	 * @param automaton
	 *            automaton
	 * @param factory
	 *            state factory
	 * @return new <code>MinimizeNwaMaxSAT2()</code> instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<LETTER, STATE> minimizeNwaMaxSAT2(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final IStateFactory<STATE> factory) throws Throwable {
		final IDoubleDeckerAutomaton<LETTER, STATE> preprocessed =
				new RemoveDeadEnds<LETTER, STATE>(mServices, automaton).getResult();
		return new MinimizeNwaMaxSat2<LETTER, STATE>(mServices, factory, preprocessed);
	}
	
	/**
	 * @param automaton
	 *            automaton
	 * @param factory
	 *            state factory
	 * @return new <code>ReduceNwaDirectSimulation()</code> instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<LETTER, STATE> reduceNwaDirectSimulation(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final IStateFactory<STATE> factory) throws Throwable {
		final IDoubleDeckerAutomaton<LETTER, STATE> preprocessed =
				new RemoveDeadEnds<LETTER, STATE>(mServices, automaton).getResult();
		return new ReduceNwaDirectSimulation<LETTER, STATE>(mServices, factory, preprocessed, false);
	}
	
	/**
	 * @param automaton
	 *            automaton
	 * @param factory
	 *            state factory
	 * @return new <code>ReduceNwaDelayedSimulation()</code> instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<LETTER, STATE> reduceNwaDelayedSimulation(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final IStateFactory<STATE> factory) throws Throwable {
		final IDoubleDeckerAutomaton<LETTER, STATE> preprocessed =
				new RemoveDeadEnds<LETTER, STATE>(mServices, automaton).getResult();
		return new ReduceNwaDelayedSimulation<LETTER, STATE>(mServices, factory, preprocessed, false);
	}
	
	/**
	 * @param automaton
	 *            automaton
	 * @param factory
	 *            state factory
	 * @return new <code>ReduceNwaDirectSimulation()</code> instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<LETTER, STATE> shrinkNwa(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final IStateFactory<STATE> factory) throws Throwable {
		final IDoubleDeckerAutomaton<LETTER, STATE> preprocessed =
				new RemoveUnreachable<LETTER, STATE>(mServices, automaton).getResult();
		return new ShrinkNwa<LETTER, STATE>(mServices, factory, preprocessed);
	}
	
	/**
	 * @param automaton
	 *            automaton
	 * @param factory
	 *            state factory
	 * @return new <code>BuchiReduce()</code> instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<LETTER, STATE> buchiReduce(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final IStateFactory<STATE> factory) throws Throwable {
		final IDoubleDeckerAutomaton<LETTER, STATE> preprocessed =
				new RemoveDeadEnds<LETTER, STATE>(mServices, automaton).getResult();
		return new BuchiReduce<LETTER, STATE>(mServices, factory, preprocessed);
	}
}
