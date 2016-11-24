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

import java.util.Collection;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.AbstractMinimizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizeNwaDD;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeDfaHopcroftArrays;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeDfaHopcroftLists;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaCombinator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaCombinator.MinimizationMethods;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaMaxSat2;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaMulti;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaMulti.Strategy;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaOverapproximation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPattern;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.ShrinkNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.arrays.MinimizeNwaMaxSAT;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed.BuchiReduce;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed.nwa.ReduceNwaDelayedSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct.nwa.ReduceNwaDirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.fair.ReduceBuchiFairDirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.fair.ReduceBuchiFairSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.ReduceNwaDirectSimulationB;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;

/**
 *
 * Objects of this class perform a single automata minimization operation
 * and provide the results of this operation.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <LCS> local control state, e.g., {@link BoogieIcfgLocation} for sequential
 * programs or a set of {@link BoogieIcfgLocation}s for parallel programs.
 * @param <LCSP> local control state provider, e.g., {@link ISLPredicate}, or
 * {@link IMLPredicate}
 */
public class AutomataMinimization<LCS, LCSP extends IPredicate> {
	
	
	private final ILogger mLogger;
	private final MinimizationResult mMinimizationResult;
	private final IDoubleDeckerAutomaton<CodeBlock, IPredicate> mMinimizedAutomaton;
	private final Map<IPredicate, IPredicate> mOldState2newState;
	private final AutomataMinimizationStatisticsGenerator mStatistics;


	public AutomataMinimization(final IUltimateServiceProvider services, 
			final INestedWordAutomaton<CodeBlock, IPredicate> operand, 
			final Minimization minimization, final boolean computeOldState2NewStateMapping,
			final int iteration, final IStateFactory<IPredicate> predicateFactoryRefinement,
			final int minimizeEveryKthIteration,
			final Collection<INestedWordAutomatonSimple<CodeBlock, IPredicate>> storedRawInterpolantAutomata,
			final INestedWordAutomaton<CodeBlock, IPredicate> interpolAutomaton,
			final int minimizationTimeout,
			final IStateFactory<IPredicate> resultCheckPredFac,
			final Function<LCSP, LCS> lcsProvider) throws AutomataOperationCanceledException {
		
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final long startTime = System.nanoTime();
		
		final Collection<Set<IPredicate>> partition = TraceAbstractionUtils.computePartition(operand, mLogger, lcsProvider); 

			// output of minimization
			
			final AutomataLibraryServices autServices = new AutomataLibraryServices(services);
			
			mMinimizationResult = doMinimizationOperation(operand, minimization,
					computeOldState2NewStateMapping, iteration, predicateFactoryRefinement, minimizeEveryKthIteration,
					storedRawInterpolantAutomata, interpolAutomaton, minimizationTimeout, partition, autServices);
			// postprocessing after minimization
			final IDoubleDeckerAutomaton<CodeBlock, IPredicate> newAbstraction;
			if (mMinimizationResult.wasNewAutomatonWasBuilt()) {
				// extract result
				try {
					assert mMinimizationResult.getRawMinimizationOutput().checkResult(resultCheckPredFac);
				} catch (final AutomataLibraryException e) {
					throw new AssertionError(e);
				}
				if (mMinimizationResult.getRawMinimizationOutput() instanceof IMinimizeNwaDD) {
					/**
					 * TODO Christian 2016-08-05: remove RemoveUnreachable() call (test thoroughly first!)
					 */
					// DoubleDecker information already present in output
					newAbstraction = (IDoubleDeckerAutomaton<CodeBlock, IPredicate>) mMinimizationResult.getRawMinimizationOutput().getResult();
					// (new RemoveUnreachable<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
					// newAbstractionRaw.getResult())).getResult();
				} else {
					// compute DoubleDecker information
					newAbstraction = (new RemoveUnreachable<>(new AutomataLibraryServices(services),
							mMinimizationResult.getRawMinimizationOutput().getResult())).getResult();
				}

				// extract Hoare annotation
				if (computeOldState2NewStateMapping) {
					if (!(mMinimizationResult.getRawMinimizationOutput() instanceof AbstractMinimizeNwa)) {
						throw new AssertionError("Hoare annotation and " + minimization + " incompatible");
					}
					final AbstractMinimizeNwa<CodeBlock, IPredicate> minimizeOpCast =
							(AbstractMinimizeNwa<CodeBlock, IPredicate>) mMinimizationResult.getRawMinimizationOutput();
					mOldState2newState = minimizeOpCast.getOldState2newState();
				} else {
					mOldState2newState = null;
				}

				// use result
				mMinimizedAutomaton = newAbstraction;

			} else {
				mMinimizedAutomaton = null;
				mOldState2newState = null;
			}
			final long statesRemovedByMinimization = operand.size() - mMinimizedAutomaton.size();
			final long automataMinimizationTime = System.nanoTime() - startTime;
			mStatistics = new AutomataMinimizationStatisticsGenerator(automataMinimizationTime, 
					mMinimizationResult.wasMinimizationAttempted(), statesRemovedByMinimization > 0, statesRemovedByMinimization);
	}

	private MinimizationResult doMinimizationOperation(final INestedWordAutomaton<CodeBlock, IPredicate> operand,
			final Minimization minimization, final boolean computeOldState2NewStateMapping, final int iteration,
			final IStateFactory<IPredicate> predicateFactoryRefinement, final int minimizeEveryKthIteration,
			final Collection<INestedWordAutomatonSimple<CodeBlock, IPredicate>> storedRawInterpolantAutomata,
			final INestedWordAutomaton<CodeBlock, IPredicate> interpolAutomaton, final int minimizationTimeout,
			final Collection<Set<IPredicate>> partition, final AutomataLibraryServices autServices)
			throws AutomataOperationCanceledException, AssertionError {
		
		final MinimizationResult minimizationResult;
		switch (minimization) {
		case MINIMIZE_SEVPA: {
			minimizationResult = new MinimizationResult(true, true, 
					new MinimizeSevpa<>(autServices, operand, partition, predicateFactoryRefinement,
							computeOldState2NewStateMapping));
			break;
		}
		case SHRINK_NWA: {
			minimizationResult = new MinimizationResult(true, true, 
					new ShrinkNwa<>(autServices, predicateFactoryRefinement, operand, partition,
					computeOldState2NewStateMapping, false, false, ShrinkNwa.SUGGESTED_RANDOM_SPLIT_SIZE, false, 0, false,
					false, true));
			break;
		}
		case NWA_COMBINATOR_PATTERN: {
			final IMinimizeNwa<CodeBlock, IPredicate> minNwa = new MinimizeNwaPattern<>(autServices, predicateFactoryRefinement,
					(IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand, partition,
					computeOldState2NewStateMapping, iteration);
			// it can happen that no minimization took place
			final boolean newAutomatonWasBuilt = (minNwa != operand);
			minimizationResult = new MinimizationResult(true, newAutomatonWasBuilt, minNwa); 
			break;
		}
		case NWA_COMBINATOR_EVERY_KTH: {
			final IMinimizeNwa<CodeBlock, IPredicate> minNwa = new MinimizeNwaPattern<>(autServices, predicateFactoryRefinement,
					(IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand, partition,
					computeOldState2NewStateMapping, minimizeEveryKthIteration, iteration);
			// it can happen that no minimization took place
			final boolean newAutomatonWasBuilt = (minNwa != operand);
			minimizationResult = new MinimizationResult(true, newAutomatonWasBuilt, minNwa); 
			throw new UnsupportedOperationException("currently unsupported - check minimizaton attemp");
		}
		case NWA_OVERAPPROXIMATION: {
			assert storedRawInterpolantAutomata != null;
			storedRawInterpolantAutomata.add(interpolAutomaton);
			final IMinimizeNwa<CodeBlock, IPredicate> minNwa = new MinimizeNwaOverapproximation<>(autServices, 
					predicateFactoryRefinement, operand, partition, computeOldState2NewStateMapping, minimizationTimeout,
					storedRawInterpolantAutomata);
			final boolean newAutomatonWasBuilt = (minNwa != operand);
			minimizationResult = new MinimizationResult(true, newAutomatonWasBuilt, minNwa); 
			throw new UnsupportedOperationException("currently unsupported - check minimizaton attemp");
		}
		case DFA_HOPCROFT_ARRAYS: {
			minimizationResult = new MinimizationResult(true, true, 
					new MinimizeDfaHopcroftArrays<>(autServices, operand,
					predicateFactoryRefinement, partition, computeOldState2NewStateMapping));
			break;
		}
		case DFA_HOPCROFT_LISTS: {
			minimizationResult = new MinimizationResult(true, true, 
					new MinimizeDfaHopcroftLists<>(autServices, operand, predicateFactoryRefinement,
					partition, computeOldState2NewStateMapping));
			break;
		}
		case NWA_MAX_SAT: {
			minimizationResult = new MinimizationResult(true, true, 
					new MinimizeNwaMaxSAT<>(autServices, predicateFactoryRefinement, operand));
			break;
		}
		case NWA_MAX_SAT2: {
			minimizationResult = new MinimizationResult(true, true, 
					new MinimizeNwaMaxSat2<>(autServices, predicateFactoryRefinement,
					(IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand, computeOldState2NewStateMapping,
					partition));
			break;
		}
		case RAQ_DIRECT_SIMULATION: {
			minimizationResult = new MinimizationResult(true, true, 
					new ReduceNwaDirectSimulation<>(autServices, predicateFactoryRefinement,
					(IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand, false, partition));
			break;
		}
		case RAQ_DIRECT_SIMULATION_B: {
			minimizationResult = new MinimizationResult(true, true, 
					new ReduceNwaDirectSimulationB<CodeBlock, IPredicate>(autServices, predicateFactoryRefinement,
					(IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand));
			break;
		}
		case NWA_COMBINATOR_MULTI_DEFAULT: {
			final IMinimizeNwa<CodeBlock, IPredicate> minNwa = new MinimizeNwaMulti<>(autServices, predicateFactoryRefinement,
					(IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand, partition,
					computeOldState2NewStateMapping);
			final boolean minimizationAttempt = ((MinimizeNwaCombinator<CodeBlock, IPredicate>) minNwa).getMode() != MinimizationMethods.NONE;
			minimizationResult = new MinimizationResult(minimizationAttempt, true, minNwa); 
			break;
		}
		case NWA_COMBINATOR_MULTI_SIMULATION: {
			final IMinimizeNwa<CodeBlock, IPredicate> minNwa = new MinimizeNwaMulti<>(autServices, predicateFactoryRefinement,
					(IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand, partition,
					computeOldState2NewStateMapping, Strategy.SIMULATION_BASED);
			final boolean minimizationAttempt = ((MinimizeNwaCombinator<CodeBlock, IPredicate>) minNwa).getMode() != MinimizationMethods.NONE;
			minimizationResult = new MinimizationResult(minimizationAttempt, true, minNwa); 
			break;
		}
		case DelayedSimulation: {
			minimizationResult = new MinimizationResult(true, true, 
					new BuchiReduce<>(autServices, predicateFactoryRefinement, operand));
			break;
		}
		case FairSimulation_WithSCC: {
			minimizationResult = new MinimizationResult(true, true, 
					new ReduceBuchiFairSimulation<>(autServices, predicateFactoryRefinement, operand, true));
			break;
		}
		case FairSimulation_WithoutSCC: {
			minimizationResult = new MinimizationResult(true, true, 
					new ReduceBuchiFairSimulation<>(autServices, predicateFactoryRefinement, operand, false));
			break;
		}
		case FairDirectSimulation: {
			minimizationResult = new MinimizationResult(true, true, 
					new ReduceBuchiFairDirectSimulation<>(autServices, predicateFactoryRefinement, operand, true));
			break;
		}
		case RaqDelayedSimulation: {
			minimizationResult = new MinimizationResult(true, true,
			new ReduceNwaDelayedSimulation<>(autServices,
					predicateFactoryRefinement, (IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand,
					false, partition));
			break;
		}
		case NONE:
			throw new IllegalArgumentException("No minimization method specified.");
		default:
			throw new AssertionError("Unknown minimization method.");
		}
		return minimizationResult;
	}

	public IDoubleDeckerAutomaton<CodeBlock, IPredicate> getMinimizedAutomaton() {
		return mMinimizedAutomaton;
	}

	public Map<IPredicate, IPredicate> getOldState2newStateMapping() {
		return mOldState2newState;
	}

	public boolean newAutomatonWasBuilt() {
		return mMinimizationResult.wasNewAutomatonWasBuilt();
	}

	public boolean wasMinimizationAttempted() {
		return mMinimizationResult.wasMinimizationAttempted();
	}
	
	public AutomataMinimizationStatisticsGenerator getStatistics() {
		return mStatistics;
	}




	private class MinimizationResult {
		private final boolean mNewAutomatonWasBuilt;
		private final boolean mMinimizationAttempt;
		private final IMinimizeNwa<CodeBlock, IPredicate> mRawMinimizationOutput;
		
		public MinimizationResult(final boolean minimizationAttempt, final boolean newAutomatonWasBuilt,
				final IMinimizeNwa<CodeBlock, IPredicate> rawMinimizationOutput) {
			super();
			mNewAutomatonWasBuilt = newAutomatonWasBuilt;
			mMinimizationAttempt = minimizationAttempt;
			mRawMinimizationOutput = rawMinimizationOutput;
		}
		public boolean wasNewAutomatonWasBuilt() {
			return mNewAutomatonWasBuilt;
		}
		public boolean wasMinimizationAttempted() {
			return mMinimizationAttempt;
		}
		public IMinimizeNwa<CodeBlock, IPredicate> getRawMinimizationOutput() {
			return mRawMinimizationOutput;
		}
		
		
	}
	
	

}
