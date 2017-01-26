/*
 * Copyright (C) 2015 Dirk Steinmetz
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.PathInvariantsGenerator.PathInvariantsBenchmarkGenerator;

/**
 * A generator for a map of invariants to {@link ControlFlowGraph.Location}s within a {@link ControlFlowGraph}, using a
 * {@link IInvariantPatternProcessor} .
 */
public final class CFGInvariantsGenerator {

	private final ILogger mLogger;
	private final IProgressMonitorService pmService;
	private PathInvariantsBenchmarkGenerator mPathInvariantsBenchmarks;
	private static boolean INIT_USE_EMPTY_PATTERNS = true;
	private static boolean USE_VARS_FROM_UNSAT_CORE_FOR_EACH_LOC = true;

	/**
	 * Create a generator for invariant maps on {@link ControlFlowGraph}s.
	 * 
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param athInvariantsBenchmarks 
	 * @param errorLocation - the location where the nested run ends
	 * @param startLocation - the location where the nested run starts
	 * @param modGlobVarManager
	 *            reserved for future use.
	 */
	public CFGInvariantsGenerator(final IUltimateServiceProvider services, PathInvariantsBenchmarkGenerator pathInvariantsBenchmarks) {
		pmService = services.getProgressMonitorService();
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mPathInvariantsBenchmarks = pathInvariantsBenchmarks;
	}

	/**
	 * Attempts to generate an invariant map for a given CFG (pair of locations and transitions) using a
	 * {@link IInvariantPatternProcessor} from the given {@link IInvariantPatternProcessorFactory}.
	 * 
	 * The {@link IInvariantPatternProcessor} will be used for up to {@link IInvariantPatternProcessor#getMaxRounds()}
	 * attempts to generate such an invariant map. If all attempts fail, this method returns null.
	 * 
	 * @param <IPT>
	 *            Invariant Pattern Type: Type used for invariant patterns
	 * @param precondition

	 * @param postcondition

	 * @param invPatternProcFactory
	 *            the factory to produce the {@link IInvariantPatternProcessor} with
	 * @return the invariant map for the set of given locations or null if the processor failed to process its invariant
	 *         patterns up to its final run.
	 */
	public <IPT> Map<IcfgLocation, IPredicate> generateInvariantsForTransitions(final List<IcfgLocation> locationsAsList, 
			final List<IcfgInternalTransition> transitions,
			final IPredicate precondition, final IPredicate postcondition, IcfgLocation startLocation, IcfgLocation errorLocation,
			final IInvariantPatternProcessorFactory<IPT> invPatternProcFactory, final boolean useVariablesFromUnsatCore, 
			final boolean useLiveVariables, final Map<IcfgLocation, Set<IProgramVar>> locs2LiveVariables,
			Map<IcfgLocation, UnmodifiableTransFormula> pathprogramLocs2Predicates, boolean usePredicates,
			boolean addWPToEeachDisjunct) {
		final IInvariantPatternProcessor<IPT> processor = invPatternProcFactory.produce(locationsAsList, transitions, precondition,
				postcondition, startLocation, errorLocation);

		mLogger.info("(Path)program has " + locationsAsList.size() + " locations");
		final Map<IcfgLocation, IPT> locs2Patterns = new HashMap<IcfgLocation, IPT>(locationsAsList.size());
		final Map<IcfgLocation, Set<IProgramVar>> locs2PatternVariables = new HashMap<IcfgLocation, Set<IProgramVar>>(locationsAsList.size());
		
		final Collection<InvariantTransitionPredicate<IPT>> predicates = new ArrayList<InvariantTransitionPredicate<IPT>>(
				transitions.size() + 2);

		final Map<TermVariable, IProgramVar> smtVars2ProgramVars = new HashMap<>();
		if (useVariablesFromUnsatCore) {
			// Compute map smt-variables to program variables
			for (final IcfgInternalTransition t : transitions) {
				// Add value-key-pairs from transitions invars to smtVars2ProgramVars
				for (final Map.Entry<IProgramVar, TermVariable> entry : t.getTransformula().getInVars().entrySet()) {
					smtVars2ProgramVars.put(entry.getValue(), entry.getKey());
				}
				// Add value-key-pairs from transitions outvars to smtVars2ProgramVars
				for (final Map.Entry<IProgramVar, TermVariable> entry : t.getTransformula().getOutVars().entrySet()) {
					smtVars2ProgramVars.put(entry.getValue(), entry.getKey());
				}
			}
		}
		Set<IProgramVar> varsFromUnsatCore = new HashSet<>();
		if (useVariablesFromUnsatCore && INIT_USE_EMPTY_PATTERNS) {
			// Execute pre-round with empty patterns for intermediate locations, so we can use the variables from the unsat core
			Map<IcfgLocation, IPredicate> resultFromPreRound = executePreRoundWithEmptyPatterns(processor, 0, varsFromUnsatCore, locs2Patterns, locs2PatternVariables,
					predicates, smtVars2ProgramVars, startLocation, errorLocation, locationsAsList, transitions,
					pathprogramLocs2Predicates, usePredicates, addWPToEeachDisjunct);
			if (resultFromPreRound != null) {
				return resultFromPreRound;
			}
		}
		for (int round = 0; round < processor.getMaxRounds(); round++) {
			// Die if we run into timeouts or are otherwise requested to cancel.
			if (!pmService.continueProcessing()) {
				throw new ToolchainCanceledException(CFGInvariantsGenerator.class);
			}

			// Start round
			processor.startRound(round);
			mLogger.info("[CFGInvariants] Round " + round + " started");

			// Build pattern map
			locs2Patterns.clear();
			locs2PatternVariables.clear();
			// Init the entry pattern with 'true' and the exit pattern with 'false'
			processor.initializeEntryAndExitPattern();
			for (final IcfgLocation location : locationsAsList) {
				if(useVariablesFromUnsatCore && USE_VARS_FROM_UNSAT_CORE_FOR_EACH_LOC) {
					locs2Patterns.put(location, processor.getInvariantPatternForLocation(location, round, varsFromUnsatCore));
				} else {
					locs2Patterns.put(location, processor.getInvariantPatternForLocation(location, round));
				}
				locs2PatternVariables.put(location, processor.getVariablesForInvariantPattern(location, round));
			}
			// add the weakest precondition of the last transition to each pattern
			if (usePredicates && pathprogramLocs2Predicates != null) {
//				addWeakestPreconditinoOfLastTransitionToPatterns(locationsAsList, processor, patterns, pathprogramLocs2WP, addWPToEeachDisjunct);
				addWP_PredicatesToInvariantPatterns(processor, locs2Patterns, locs2PatternVariables, pathprogramLocs2Predicates, addWPToEeachDisjunct);
			}
			mLogger.info("[CFGInvariants] Built pattern map.");

			// Build transition predicates
			predicates.clear();
			int maxSizeOfTemplate = 1;
			for (final IcfgInternalTransition transition : transitions) {
				final IPT invStart = locs2Patterns.get(transition.getSource());
				final IPT invEnd = locs2Patterns.get(transition.getTarget());
				predicates.add(new InvariantTransitionPredicate<IPT>(invStart, invEnd, transition.getSource(), transition.getTarget(), 
						locs2PatternVariables.get(transition.getSource()),
						locs2PatternVariables.get(transition.getTarget()), transition.getTransformula()));
				// Compute the max. size of template
				int sizeOfTemplate1 = ((LinearInequalityInvariantPatternProcessor)processor).getTotalNumberOfConjunctsInPattern(
						(Collection<Collection<AbstractLinearInvariantPattern>>) invStart);
				int sizeOfTemplate2 = ((LinearInequalityInvariantPatternProcessor)processor).getTotalNumberOfConjunctsInPattern(
						(Collection<Collection<AbstractLinearInvariantPattern>>) invEnd);
				if (sizeOfTemplate1 > sizeOfTemplate2) {
					if (sizeOfTemplate1 > maxSizeOfTemplate) {
						maxSizeOfTemplate = sizeOfTemplate1;
					}
				} else {
					if (sizeOfTemplate2 > maxSizeOfTemplate) {
						maxSizeOfTemplate = sizeOfTemplate2;
					}
				}
			}
			mLogger.info("[CFGInvariants] Built " + predicates.size() + " predicates.");
			
			// Set the benchmarks
			mPathInvariantsBenchmarks.setPathInvariantsData(maxSizeOfTemplate, round);
			
			// Attempt to find a valid configuration
			if (processor.hasValidConfiguration(predicates, round)) {
				mLogger.info("[CFGInvariants] Found valid " + "configuration in round " + round + ".");

				final Map<IcfgLocation, IPredicate> result = new HashMap<IcfgLocation, IPredicate>(
						locationsAsList.size());
				// Extract the values for all pattern coefficients
				processor.extractValuesForPatternCoefficients();
				// Apply configuration for each pair (location, pattern) in order to obtain a predicate for each location.
				for (final IcfgLocation location : locationsAsList) {
					result.put(location, processor.applyConfiguration(locs2Patterns.get(location)));
				}
				return result;
			} else {
				// If no configuration could have been found, the constraints may be unsatisfiable
				if (useVariablesFromUnsatCore) {
					final Collection<TermVariable> smtVarsFromUnsatCore = ((LinearInequalityInvariantPatternProcessor)processor).getVarsFromUnsatCore();
					if (smtVarsFromUnsatCore != null) {
						mLogger.info(smtVarsFromUnsatCore.size() + " out of " + smtVars2ProgramVars.size() + " SMT variables in unsat core");
						// The result in pattern processor was 'unsat'
						varsFromUnsatCore = new HashSet<>(smtVarsFromUnsatCore.size());
						for (final TermVariable smtVar : smtVarsFromUnsatCore) {
							if (smtVars2ProgramVars.get(smtVar) != null) {
								varsFromUnsatCore.add(smtVars2ProgramVars.get(smtVar));
							}
						}
						mLogger.info(varsFromUnsatCore.size() + " out of " + (new HashSet<>(smtVars2ProgramVars.values())).size() + " program variables in unsat core");
					} else {
						// The result in pattern processor was 'unknown', so reset varsFromUnsatCore to null
						varsFromUnsatCore = null;
					}
				}
			}
		}

		mLogger.info(
				"[CFGInvariants] No valid configuration " + "within round bound (" + processor.getMaxRounds() + ").");
		return null;
	}
	
	
	
	private <IPT> void addWP_PredicatesToInvariantPatterns(final IInvariantPatternProcessor<IPT> processor, final Map<IcfgLocation, IPT> patterns,
			final Map<IcfgLocation, Set<IProgramVar>> locs2PatternVariables,
			Map<IcfgLocation, UnmodifiableTransFormula> pathprogramLocs2WP,
			boolean addWPToEeachDisjunct) {
		mLogger.info("Add weakest precondition to invariant patterns.");
		if (addWPToEeachDisjunct) {
			for (Map.Entry<IcfgLocation, UnmodifiableTransFormula> entry : pathprogramLocs2WP.entrySet()) {
				mLogger.info("Loc: " + entry.getKey() +  " WP: " + entry.getValue());
				IPT newPattern = processor.addTransFormulaToEachConjunctInPattern(patterns.get(entry.getKey()), entry.getValue());
				patterns.put(entry.getKey(), newPattern);
				Set<IProgramVar> varsInWP = new HashSet<>(entry.getValue().getInVars().keySet());
				varsInWP.addAll(entry.getValue().getOutVars().keySet());
				// Add variables that are already assoc. with this location.
				varsInWP.addAll(locs2PatternVariables.get(entry.getKey()));
				locs2PatternVariables.put(entry.getKey(), varsInWP);
			}
		} else {
			for (Map.Entry<IcfgLocation, UnmodifiableTransFormula> entry : pathprogramLocs2WP.entrySet()) {
				IPT newPattern = processor.addTransFormulaAsAdditionalDisjunctToPattern(patterns.get(entry.getKey()), entry.getValue());
				patterns.put(entry.getKey(), newPattern);
				Set<IProgramVar> varsInWP = new HashSet<>(entry.getValue().getInVars().keySet());
				varsInWP.addAll(entry.getValue().getOutVars().keySet());
				// Add variables that are already assoc. with this location.
				varsInWP.addAll(locs2PatternVariables.get(entry.getKey()));
				locs2PatternVariables.put(entry.getKey(), varsInWP);
			}
		}
	}

	/**
	 * Check if you can find an invariant with empty patterns for intermediate locations.
	 * @return
	 */
	private <IPT> Map<IcfgLocation, IPredicate> executePreRoundWithEmptyPatterns(final IInvariantPatternProcessor<IPT> processor, int round, Set<IProgramVar> varsFromUnsatCore,
			final Map<IcfgLocation, IPT> locs2Patterns, final Map<IcfgLocation, Set<IProgramVar>> locs2PatternVariables,
			final Collection<InvariantTransitionPredicate<IPT>> predicates,
			final Map<TermVariable, IProgramVar> smtVars2ProgramVars, IcfgLocation startLocation, IcfgLocation errorLocation, 
			final List<IcfgLocation> locationsAsList, final List<IcfgInternalTransition> transitions,
			Map<IcfgLocation, UnmodifiableTransFormula> pathprogramLocs2Predicates, boolean usePredicates,
			boolean addWPToEeachDisjunct) {
		// Start round -1 (because it's the round with empty pattern for each location)
		round = -1;
		processor.startRound(round);
		mLogger.info("Pre-round with empty patterns for intermediate locations started...");
		
		
		// Build pattern map
		locs2Patterns.clear();
		locs2PatternVariables.clear();
		// Init the entry pattern with 'true' and the exit pattern with 'false'
		processor.initializeEntryAndExitPattern();
		for (final IcfgLocation location : locationsAsList) {
			final IPT invPattern;
			if (location.equals(startLocation)) {
				invPattern = processor.getEntryInvariantPattern();
			} else if (location.equals(errorLocation)) {
				invPattern = processor.getExitInvariantPattern();
			} else {
				// Use for intermediate locations an empty pattern
				invPattern = processor.getEmptyInvariantPattern();
			}
			locs2Patterns.put(location, invPattern);
			locs2PatternVariables.put(location, Collections.emptySet());
		}
		mLogger.info("Built (empty) pattern map");
		// add the weakest precondition of the last transition to each pattern
		if (usePredicates && pathprogramLocs2Predicates != null) {
			addWP_PredicatesToInvariantPatterns(processor, locs2Patterns, locs2PatternVariables, pathprogramLocs2Predicates, addWPToEeachDisjunct);
		}

		// Build transition predicates
		predicates.clear();
		for (final IcfgInternalTransition transition : transitions) {
			final IPT invStart = locs2Patterns.get(transition.getSource());
			final IPT invEnd = locs2Patterns.get(transition.getTarget());
			predicates.add(new InvariantTransitionPredicate<IPT>(invStart, invEnd, transition.getSource(), transition.getTarget(), 
					locs2PatternVariables.get(transition.getSource()), locs2PatternVariables.get(transition.getTarget()),
					transition.getTransformula()));
		}
		mLogger.info("Built " + predicates.size() + " transition predicates.");

		// Attempt to find a valid configuration
		if (processor.hasValidConfiguration(predicates, round)) {
			mLogger.info("Found valid " + "configuration in pre-round.");
			final Map<IcfgLocation, IPredicate> result = new HashMap<IcfgLocation, IPredicate>(
					locationsAsList.size());
			// Extract the values for all pattern coefficients
			processor.extractValuesForPatternCoefficients();
			// Apply configuration for each pair (location, pattern) in order to obtain a predicate for each location.
			for (final IcfgLocation location : locationsAsList) {
				IPredicate p = processor.applyConfiguration(locs2Patterns.get(location));
				result.put(location, p);
			}
			return result;
		} else {
			// If no configuration could have been found, the constraints may be unsatisfiable
			final Collection<TermVariable> smtVarsFromUnsatCore = ((LinearInequalityInvariantPatternProcessor)processor).getVarsFromUnsatCore();
			if (smtVarsFromUnsatCore != null) {
				mLogger.info(smtVarsFromUnsatCore.size() + " out of " + smtVars2ProgramVars.size() + " SMT variables in unsat core");
				// The result in pattern processor was 'unsat'
				// varsFromUnsatCore = new HashSet<>(smtVarsFromUnsatCore.size());
				for (final TermVariable smtVar : smtVarsFromUnsatCore) {
					if (smtVars2ProgramVars.get(smtVar) != null) {
						varsFromUnsatCore.add(smtVars2ProgramVars.get(smtVar));
					}
				}
				mLogger.info(varsFromUnsatCore.size() + " out of " + (new HashSet<>(smtVars2ProgramVars.values())).size() + " program variables in unsat core");
			} else {
				// The result in pattern processor was 'unknown', so reset varsFromUnsatCore to null
				varsFromUnsatCore = null;
			}
		}
		mLogger.info("No valid configuration found in pre-round.");
		return null;
	}
}
