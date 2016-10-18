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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct.nwa.ReduceNwaDirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.ReduceNwaDirectSimulationB;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;

/**
 *
 * Objects of this class perform a single automata minimization operation
 * and provide the results of this operation.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <LCS> local control state, e.g., {@link ProgramPoint} for sequential
 * programs or a set of {@link ProgramPoint}s for parallel programs.
 * @param <LCSP> local control state provider, e.g., {@link ISLPredicate}, or
 * {@link IMLPredicate}
 */
public class AutomataMinimization<LCS, LCSP extends IPredicate> {
	
	
	private final ILogger mLogger;
	private final IDoubleDeckerAutomaton<CodeBlock, IPredicate> mMinimizedAutomaton;
	private final Map<IPredicate, IPredicate> mOldState2newState;
	private final boolean mWasMinimized;
	private final boolean mMinimizationAttempt;

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
		
		final Collection<Set<IPredicate>> partition = TraceAbstractionUtils.computePartition(operand, mLogger, lcsProvider); 

			// output of minimization
			final IMinimizeNwa<CodeBlock, IPredicate> newAbstractionRaw;
			final AutomataLibraryServices autServices = new AutomataLibraryServices(services);
			
			switch (minimization) {
			case MINIMIZE_SEVPA: {
				newAbstractionRaw = new MinimizeSevpa<>(autServices, operand, partition, predicateFactoryRefinement,
						computeOldState2NewStateMapping);
				mWasMinimized = true;
				mMinimizationAttempt = true;
				break;
			}
			case SHRINK_NWA: {
				newAbstractionRaw = new ShrinkNwa<>(autServices, predicateFactoryRefinement, operand, partition,
						computeOldState2NewStateMapping, false, false, ShrinkNwa.SUGGESTED_RANDOM_SPLIT_SIZE, false, 0, false,
						false, true);
				mWasMinimized = true;
				mMinimizationAttempt = true;
				break;
			}
			case NWA_COMBINATOR_PATTERN: {
				newAbstractionRaw = new MinimizeNwaPattern<>(autServices, predicateFactoryRefinement,
						(IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand, partition,
						computeOldState2NewStateMapping, iteration);
				// it can happen that no minimization took place
				mWasMinimized = (newAbstractionRaw == operand);
				mMinimizationAttempt = true;
				break;
			}
			case NWA_COMBINATOR_EVERY_KTH: {
				newAbstractionRaw = new MinimizeNwaPattern<>(autServices, predicateFactoryRefinement,
						(IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand, partition,
						computeOldState2NewStateMapping, minimizeEveryKthIteration, iteration);
				// it can happen that no minimization took place
				mWasMinimized = (newAbstractionRaw == operand);
				throw new UnsupportedOperationException("currently unsupported - check minimizaton attemp");
			}
			case NWA_OVERAPPROXIMATION: {
				assert storedRawInterpolantAutomata != null;
				storedRawInterpolantAutomata.add(interpolAutomaton);
				newAbstractionRaw = new MinimizeNwaOverapproximation<>(autServices, predicateFactoryRefinement,
						operand, partition, computeOldState2NewStateMapping, minimizationTimeout,
						storedRawInterpolantAutomata);
				mWasMinimized = true;
				throw new UnsupportedOperationException("currently unsupported - check minimizaton attemp");
			}
			case DFA_HOPCROFT_ARRAYS: {
				newAbstractionRaw = new MinimizeDfaHopcroftArrays<>(autServices, operand,
						predicateFactoryRefinement, partition, computeOldState2NewStateMapping);
				mWasMinimized = true;
				mMinimizationAttempt = true;
				break;
			}
			case DFA_HOPCROFT_LISTS: {
				newAbstractionRaw = new MinimizeDfaHopcroftLists<>(autServices, operand, predicateFactoryRefinement,
						partition, computeOldState2NewStateMapping);
				mWasMinimized = true;
				mMinimizationAttempt = true;
				break;
			}
			case NWA_MAX_SAT: {
				newAbstractionRaw = new MinimizeNwaMaxSAT<>(autServices, predicateFactoryRefinement, operand);
				mWasMinimized = true;
				mMinimizationAttempt = true;
				break;
			}
			case NWA_MAX_SAT2: {
				newAbstractionRaw = new MinimizeNwaMaxSat2<>(autServices, predicateFactoryRefinement,
						(IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand, computeOldState2NewStateMapping,
						partition);
				mWasMinimized = true;
				mMinimizationAttempt = true;
				break;
			}
			case RAQ_DIRECT_SIMULATION: {
				newAbstractionRaw = new ReduceNwaDirectSimulation<>(autServices, predicateFactoryRefinement,
						(IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand, false, partition);
				mWasMinimized = true;
				mMinimizationAttempt = true;
				break;
			}
			case RAQ_DIRECT_SIMULATION_B: {
				newAbstractionRaw = new ReduceNwaDirectSimulationB<CodeBlock, IPredicate>(autServices, predicateFactoryRefinement,
						(IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand);
				mWasMinimized = true;
				mMinimizationAttempt = true;
				break;
			}
			case NWA_COMBINATOR_MULTI_DEFAULT: {
				newAbstractionRaw = new MinimizeNwaMulti<>(autServices, predicateFactoryRefinement,
						(IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand, partition,
						computeOldState2NewStateMapping);
				mWasMinimized = true;
				mMinimizationAttempt = ((MinimizeNwaCombinator<CodeBlock, IPredicate>) newAbstractionRaw).getMode() != MinimizationMethods.NONE;
				break;
			}
			case NWA_COMBINATOR_MULTI_SIMULATION: {
				newAbstractionRaw = new MinimizeNwaMulti<>(autServices, predicateFactoryRefinement,
						(IDoubleDeckerAutomaton<CodeBlock, IPredicate>) operand, partition,
						computeOldState2NewStateMapping, Strategy.SIMULATION_BASED);
				mWasMinimized = true;
				mMinimizationAttempt = ((MinimizeNwaCombinator<CodeBlock, IPredicate>) newAbstractionRaw).getMode() != MinimizationMethods.NONE;
				break;
			}
			case NONE:
				throw new IllegalArgumentException("No minimization method specified.");
			default:
				throw new AssertionError("Unknown minimization method.");
			}
			// postprocessing after minimization
			final IDoubleDeckerAutomaton<CodeBlock, IPredicate> newAbstraction;
			if (mWasMinimized) {
				// extract result
				try {
					assert newAbstractionRaw.checkResult(resultCheckPredFac);
				} catch (final AutomataLibraryException e) {
					throw new AssertionError(e);
				}
				if (newAbstractionRaw instanceof IMinimizeNwaDD) {
					/**
					 * TODO Christian 2016-08-05: remove RemoveUnreachable() call (test thoroughly first!)
					 */
					// DoubleDecker information already present in output
					newAbstraction = (IDoubleDeckerAutomaton<CodeBlock, IPredicate>) newAbstractionRaw.getResult();
					// (new RemoveUnreachable<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
					// newAbstractionRaw.getResult())).getResult();
				} else {
					// compute DoubleDecker information
					newAbstraction = (new RemoveUnreachable<>(new AutomataLibraryServices(services),
							newAbstractionRaw.getResult())).getResult();
				}

				// extract Hoare annotation
				if (computeOldState2NewStateMapping) {
					if (!(newAbstractionRaw instanceof AbstractMinimizeNwa)) {
						throw new AssertionError("Hoare annotation and " + minimization + " incompatible");
					}
					final AbstractMinimizeNwa<CodeBlock, IPredicate> minimizeOpCast =
							(AbstractMinimizeNwa<CodeBlock, IPredicate>) newAbstractionRaw;
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
	}

	public IDoubleDeckerAutomaton<CodeBlock, IPredicate> getMinimizedAutomaton() {
		return mMinimizedAutomaton;
	}

	public Map<IPredicate, IPredicate> getOldState2newStateMapping() {
		return mOldState2newState;
	}

	public boolean wasMinimized() {
		return mWasMinimized;
	}

	public boolean wasMinimizationAttempted() {
		return mMinimizationAttempt;
	}
	
	
	

}
