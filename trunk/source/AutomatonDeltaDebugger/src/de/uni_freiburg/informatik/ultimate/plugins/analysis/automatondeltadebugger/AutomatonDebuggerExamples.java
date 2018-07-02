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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementNCSB;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Complement;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaOverapproximation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSat;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSatDirect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSatDirectBi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.ShrinkNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.arrays.MinimizeNwaMaxSAT;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed.BuchiReduce;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed.nwa.ReduceNwaDelayedSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct.nwa.ReduceNwaDirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.fair.ReduceBuchiFairDirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble.ReduceNwaDelayedFullMultipebbleSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble.ReduceNwaDirectFullMultipebbleSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.CompareSimulations;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.DirectSimulationComparison;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.ReduceNwaDelayedSimulationB;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.ReduceNwaDirectSimulationB;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * Examples used by delta debugger.
 * <p>
 * NOTE: Users may insert their sample code as a new method and leave it here.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
@SuppressWarnings({ "squid:S00112", "squid:S1452",
		"checkstyle:com.puppycrawl.tools.checkstyle.checks.metrics.ClassDataAbstractionCouplingCheck" })
public class AutomatonDebuggerExamples {
	private final AutomataLibraryServices mServices;

	/**
	 * @param services
	 *            Ultimate services.
	 */
	public AutomatonDebuggerExamples(final IUltimateServiceProvider services) {
		mServices = new AutomataLibraryServices(services);
	}

	/**
	 * Implemented operations for quick usage.
	 * <p>
	 * NOTE: If another operation is supported, add a value here.
	 */
	public enum EOperationType {
		/**
		 * Used for default settings to inform user that the method was not selected.
		 */
		EXCEPTION_DUMMY,
		/**
		 * {@link MinimizeNwaMaxSAT}.
		 */
		MINIMIZE_NWA_MAXSAT,
		/**
		 * {@link MinimizeNwaPmaxSat}.
		 */
		MINIMIZE_NWA_PMAXSAT,
		/**
		 * {@link MinimizeNwaPmaxSat}.
		 */
		MINIMIZE_NWA_PMAXSAT_ASYMMETRIC,
		/**
		 * {@link MinimizeNwaPmaxSatAsymmetric}.
		 */
		REDUCE_NWA_DIRECT_SIMULATION,
		/**
		 * {@link ReduceNwaDirectSimulationB}.
		 */
		REDUCE_NWA_DIRECT_SIMULATION_B,
		/**
		 * {@link ReduceNwaDelayedSimulation}.
		 */
		REDUCE_NWA_DELAYED_SIMULATION,
		/**
		 * {@link ReduceNwaDelayedSimulationB}.
		 */
		REDUCE_NWA_DELAYED_SIMULATION_B,
		/**
		 * {@link ReduceNwaDelayedFullMultipebbleSimulation}.
		 */
		REDUCE_NWA_DELAYED_FULL_MULTIPEBBLE_SIMULATION,
		/**
		 * {@link ShrinkNwa}.
		 */
		SHRINK_NWA,
		/**
		 * {@link BuchiComplementNCSB}.
		 */
		BUCHI_COMPLEMENT_NCSB,
		/**
		 * {@link BuchiReduce}.
		 */
		BUCHI_REDUCE,
		/**
		 * {@link Complement}.
		 */
		COMPLEMENT,
		/**
		 * {@link MinimizeNwaOverapproximation}.
		 */
		MINIMIZE_NWA_OVERAPPROXIMATION,
		/**
		 * {@link RemoveDeadEnds}.
		 */
		REMOVE_DEAD_ENDS,
		/**
		 * {@link RemoveNonLiveStates}.
		 */
		REMOVE_NON_LIVE_STATES,
		/**
		 * {@link DirectSimulationComparison}.
		 */
		DIRECT_SIMULATION_COMPARISON,
		/**
		 * {@link ReduceNwaDirectFullMultipebbleSimulation}.
		 */
		REDUCE_NWA_DIRECT_FULL_MULTIPEBBLE_SIMULATION,
		/**
		 * {@link CompareSimulations}.
		 */
		COMPARE_SIMULATIONS,
		/**
		 * {@link ReduceBuchiFairDirectSimulation}.
		 */
		REDUCE_BUCHI_FAIR_DIRECT_SIMULATION
	}

	/**
	 * Getter for an {@link IOperation}.
	 *
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
	@SuppressWarnings({ "squid:MethodCyclomaticComplexity",
			"checkstyle:com.puppycrawl.tools.checkstyle.checks.metrics.JavaNCSSCheck" })
	public IOperation<String, String, ? super StringFactory> getOperation(final EOperationType type,
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IOperation<String, String, ? super StringFactory> operation;
		switch (type) {
			case EXCEPTION_DUMMY:
				throw new IllegalArgumentException("Select a valid operation for delta debugging.");

			case MINIMIZE_NWA_MAXSAT:
				operation = minimizeNwaMaxSat(automaton, factory);
				break;

			case MINIMIZE_NWA_PMAXSAT:
				operation = minimizeNwaPmaxSat(automaton, factory);
				break;

			case MINIMIZE_NWA_PMAXSAT_ASYMMETRIC:
				operation = minimizeNwaPmaxSatAsymmetric(automaton, factory);
				break;

			case REDUCE_NWA_DIRECT_SIMULATION:
				operation = reduceNwaDirectSimulation(automaton, factory);
				break;

			case REDUCE_NWA_DIRECT_SIMULATION_B:
				operation = reduceNwaDirectSimulationB(automaton, factory);
				break;

			case REDUCE_NWA_DELAYED_SIMULATION:
				operation = reduceNwaDelayedSimulation(automaton, factory);
				break;

			case REDUCE_NWA_DELAYED_SIMULATION_B:
				operation = reduceNwaDelayedSimulationB(automaton, factory);
				break;

			case REDUCE_NWA_DELAYED_FULL_MULTIPEBBLE_SIMULATION:
				operation = reduceNwaDelayedFullMultipebbleSimulation(automaton, factory);
				break;

			case SHRINK_NWA:
				operation = shrinkNwa(automaton, factory);
				break;

			case BUCHI_COMPLEMENT_NCSB:
				operation = buchiComplementNcsb(automaton, factory);
				break;

			case BUCHI_REDUCE:
				operation = buchiReduce(automaton, factory);
				break;

			case COMPLEMENT:
				operation = complement(automaton, factory);
				break;

			case MINIMIZE_NWA_OVERAPPROXIMATION:
				operation = minimizeNwaOverapproximation(automaton, factory);
				break;

			case REMOVE_DEAD_ENDS:
				operation = removeDeadEnds(automaton);
				break;

			case REMOVE_NON_LIVE_STATES:
				operation = removeNonLiveStates(automaton);
				break;

			case DIRECT_SIMULATION_COMPARISON:
				operation = directSimulationComparison(automaton, factory);
				break;

			case REDUCE_NWA_DIRECT_FULL_MULTIPEBBLE_SIMULATION:
				operation = reduceNwaDirectFullMultipebbleSimulation(automaton, factory);
				break;

			case COMPARE_SIMULATIONS:
				operation = compareSimulations(automaton, factory);
				break;

			case REDUCE_BUCHI_FAIR_DIRECT_SIMULATION:
				operation = reduceBuchiFairDirectSimulation(automaton, factory);
				break;

			default:
				throw new IllegalArgumentException("Unknown operation.");
		}
		return operation;
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link MinimizeNwaMaxSAT} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> minimizeNwaMaxSat(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IDoubleDeckerAutomaton<String, String> preprocessed =
				new RemoveUnreachable<>(mServices, automaton).getResult();
		return new MinimizeNwaMaxSAT<>(mServices, factory, preprocessed);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link MinimizeNwaMaxSAT2} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> minimizeNwaPmaxSat(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IDoubleDeckerAutomaton<String, String> preprocessed =
				new RemoveDeadEnds<>(mServices, automaton).getResult();
		return new MinimizeNwaPmaxSatDirectBi<>(mServices, factory, preprocessed);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link ReduceNwaDirectSimulation} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> reduceNwaDirectSimulation(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IDoubleDeckerAutomaton<String, String> preprocessed =
				new RemoveDeadEnds<>(mServices, automaton).getResult();
		return new ReduceNwaDirectSimulation<>(mServices, factory, preprocessed, false);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link ReduceNwaDirectSimulationB} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> reduceNwaDirectSimulationB(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IDoubleDeckerAutomaton<String, String> preprocessed =
				new RemoveDeadEnds<>(mServices, automaton).getResult();
		return new ReduceNwaDirectSimulationB<>(mServices, factory, preprocessed);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link ReduceNwaDelayedSimulation} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> reduceNwaDelayedSimulation(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IDoubleDeckerAutomaton<String, String> preprocessed =
				new RemoveDeadEnds<>(mServices, automaton).getResult();
		return new ReduceNwaDelayedSimulation<>(mServices, factory, preprocessed, false);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link ReduceNwaDelayedSimulationB} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> reduceNwaDelayedSimulationB(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IDoubleDeckerAutomaton<String, String> preprocessed =
				new RemoveNonLiveStates<>(mServices, automaton).getResult();
		return new ReduceNwaDelayedSimulationB<>(mServices, factory, preprocessed);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link ReduceNwaDelayedFullMultipebbleSimulation} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> reduceNwaDelayedFullMultipebbleSimulation(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IDoubleDeckerAutomaton<String, String> preprocessed =
				new RemoveUnreachable<>(mServices, automaton).getResult();
		return new ReduceNwaDelayedFullMultipebbleSimulation<>(mServices, factory, preprocessed);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link ReduceNwaDirectSimulation} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> shrinkNwa(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IDoubleDeckerAutomaton<String, String> preprocessed =
				new RemoveUnreachable<>(mServices, automaton).getResult();
		return new ShrinkNwa<>(mServices, factory, preprocessed);
	}

	public IOperation<String, String, ? super StringFactory> buchiComplementNcsb(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		return new BuchiComplementNCSB<>(mServices, factory, automaton);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link BuchiReduce} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> buchiReduce(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IDoubleDeckerAutomaton<String, String> preprocessed =
				new RemoveDeadEnds<>(mServices, automaton).getResult();
		return new BuchiReduce<>(mServices, factory, preprocessed);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@code Complement()} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> complement(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		return new Complement<>(mServices, factory, automaton);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link MinimizeNwaOverapproximation} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> minimizeNwaOverapproximation(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IDoubleDeckerAutomaton<String, String> preprocessed =
				new RemoveUnreachable<>(mServices, automaton).getResult();
		return new MinimizeNwaOverapproximation<>(mServices, factory, preprocessed);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @return new {@link RemoveDeadEnds} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory>
			removeDeadEnds(final INestedWordAutomaton<String, String> automaton) throws Throwable {
		return new RemoveDeadEnds<>(mServices, automaton);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @return new {@link RemoveNonLiveStates} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory>
			removeNonLiveStates(final INestedWordAutomaton<String, String> automaton) throws Throwable {
		return new RemoveNonLiveStates<>(mServices, automaton);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link DirectSimulationComparison} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> directSimulationComparison(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		return new DirectSimulationComparison<>(mServices, factory, automaton);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link ReduceNwaDirectFullMultipebbleSimulation} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> reduceNwaDirectFullMultipebbleSimulation(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IDoubleDeckerAutomaton<String, String> preprocessed =
				new RemoveUnreachable<>(mServices, automaton).getResult();
		return new ReduceNwaDirectFullMultipebbleSimulation<>(mServices, factory, preprocessed);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link CompareSimulations} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> compareSimulations(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IDoubleDeckerAutomaton<String, String> preprocessed =
				new RemoveUnreachable<>(mServices, automaton).getResult();
		return new CompareSimulations<>(mServices, factory, preprocessed);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link MinimizeNwaPmaxSatDirect} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> minimizeNwaPmaxSatAsymmetric(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IDoubleDeckerAutomaton<String, String> preprocessed =
				new RemoveDeadEnds<>(mServices, automaton).getResult();
		return new MinimizeNwaPmaxSatDirect<>(mServices, factory, preprocessed);
	}

	/**
	 * @param automaton
	 *            The automaton.
	 * @param factory
	 *            state factory
	 * @return new {@link ReduceBuchiFairDirectSimulation} instance
	 * @throws Throwable
	 *             when error occurs
	 */
	public IOperation<String, String, ? super StringFactory> reduceBuchiFairDirectSimulation(
			final INestedWordAutomaton<String, String> automaton, final StringFactory factory) throws Throwable {
		final IDoubleDeckerAutomaton<String, String> preprocessed =
				new RemoveDeadEnds<>(mServices, automaton).getResult();
		return new ReduceBuchiFairDirectSimulation<>(mServices, factory, preprocessed);
	}
}
