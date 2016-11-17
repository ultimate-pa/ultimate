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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Location;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Transition;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * A generator for a map of invariants to {@link ControlFlowGraph.Location}s within a {@link ControlFlowGraph}, using a
 * {@link IInvariantPatternProcessor} .
 */
public final class CFGInvariantsGenerator {

	private final ILogger logService;
	private final IProgressMonitorService pmService;
	

	/**
	 * Create a generator for invariant maps on {@link ControlFlowGraph}s.
	 * 
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param modGlobVarManager
	 *            reserved for future use.
	 */
	public CFGInvariantsGenerator(final IUltimateServiceProvider services,
			final ModifiableGlobalVariableManager modGlobVarManager) {
		pmService = services.getProgressMonitorService();
		logService = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

//	/**
//	 * Attempts to generate an invariant map on a given {@link ControlFlowGraph} using a
//	 * {@link IInvariantPatternProcessor} from the given {@link IInvariantPatternProcessorFactory}.
//	 * 
//	 * The {@link IInvariantPatternProcessor} will be used for up to {@link IInvariantPatternProcessor#getMaxRounds()}
//	 * attempts to generate such an invariant map. If all attempts fail, this method returns null.
//	 * 
//	 * @param <IPT>
//	 *            Invariant Pattern Type: Type used for invariant patterns
//	 * @param cfg
//	 *            the ControlFlowGraph to generate an invariant map on
//	 * @param precondition
//	 *            the invariant on the {@link ControlFlowGraph#getEntry()} of cfg
//	 * @param postcondition
//	 *            the invariant on the {@link ControlFlowGraph#getExit()} of cfg
//	 * @param invPatternProcFactory
//	 *            the factory to produce the {@link IInvariantPatternProcessor} with
//	 * @return the invariant map for the locations of cfg or null if the processor failed to process its invariant
//	 *         patterns up to its final run.
//	 */
//	public <IPT> Map<Location, IPredicate> generateInvariantsFromCFG(final ControlFlowGraph cfg,
//			final IPredicate precondition, final IPredicate postcondition,
//			final IInvariantPatternProcessorFactory<IPT> invPatternProcFactory, final boolean useVariablesFromUnsatCore, 
//			final boolean useLiveVariables, final Set<IProgramVar> liveVariables) {
//		final IInvariantPatternProcessor<IPT> processor = invPatternProcFactory.produce(cfg, precondition,
//				postcondition);
//
//		final Collection<Location> locations = cfg.getLocations();
//		logService.info("(Path)program has " + locations.size() + " locations");
//		final Map<Location, IPT> patterns = new HashMap<Location, IPT>(locations.size());
//		final Collection<Transition> transitions = cfg.getTransitions();
//		final Collection<InvariantTransitionPredicate<IPT>> predicates = new ArrayList<InvariantTransitionPredicate<IPT>>(
//				transitions.size() + 2);
//		
//		Map<TermVariable, IProgramVar> smtVars2ProgramVars = new HashMap<>();
//		if (useVariablesFromUnsatCore) {
//			// Compute map smt-variables to program variables
//			for (Transition t : transitions) {
//				// Add value-key-pairs from transitions invars to smtVars2ProgramVars
//				for (Map.Entry<IProgramVar, TermVariable> entry : t.getTransFormula().getInVars().entrySet()) {
//					smtVars2ProgramVars.put(entry.getValue(), entry.getKey());
//				}
//				// Add value-key-pairs from transitions outvars to smtVars2ProgramVars
//				for (Map.Entry<IProgramVar, TermVariable> entry : t.getTransFormula().getOutVars().entrySet()) {
//					smtVars2ProgramVars.put(entry.getValue(), entry.getKey());
//				}
//			}
//		}
//		
//		Set<IProgramVar> varsFromUnsatCore = null;
//
//		for (int round = 0; round < processor.getMaxRounds(); round++) {
//			// Die if we run into timeouts or are otherwise requested to cancel.
//			if (!pmService.continueProcessing()) {
//				throw new ToolchainCanceledException(CFGInvariantsGenerator.class);
//			}
//
//			// Start round
//			processor.startRound(round, useLiveVariables, liveVariables, useVariablesFromUnsatCore, varsFromUnsatCore);
//			logService.info("[CFGInvariants] Round " + round + " started");
//
//			// Build pattern map
//			patterns.clear();
//			for (final Location location : locations) {
//				patterns.put(location, processor.getInvariantPatternForLocation(location, round));
//			}
//			logService.info("[CFGInvariants] Built pattern map.");
//
//			// Build transition predicates
//			predicates.clear();
//			for (final Transition transition : transitions) {
//				final IPT invStart = patterns.get(transition.getStart());
//				final IPT invEnd = patterns.get(transition.getEnd());
//				predicates.add(new InvariantTransitionPredicate<IPT>(invStart, invEnd, transition.getTransFormula()));
//			}
//			logService.info("[CFGInvariants] Built " + predicates.size() + " predicates.");
//
//			// Attempt to find a valid configuration
//			if (processor.hasValidConfiguration(predicates, round)) {
//				logService.info("[CFGInvariants] Found valid " + "configuration in round " + round + ".");
//
//				final Map<Location, IPredicate> result = new HashMap<ControlFlowGraph.Location, IPredicate>(
//						locations.size());
//				for (final Location location : locations) {
//					result.put(location, processor.applyConfiguration(patterns.get(location)));
//				}
//				return result;
//			} else {
//				// If no configuration could have been found, the constraints may be unsatisfiable
//				if (useVariablesFromUnsatCore) {
//					Collection<TermVariable> smtVarsFromUnsatCore = ((LinearInequalityInvariantPatternProcessor)processor).getVarsFromUnsatCore();
//					if (smtVarsFromUnsatCore != null) {
//						// The result in pattern processor was 'unsat'
//						varsFromUnsatCore = new HashSet<>(smtVarsFromUnsatCore.size());
//						for (TermVariable smtVar : smtVarsFromUnsatCore) {
//							varsFromUnsatCore.add(smtVars2ProgramVars.get(smtVar));
//						}
//					} else {
//						// The result in pattern processor was 'unknown', so reset varsFromUnsatCore to null
//						varsFromUnsatCore = null;
//					}
//				}
//			}
//		}
//
//		logService.info(
//				"[CFGInvariants] No valid configuration " + "within round bound (" + processor.getMaxRounds() + ").");
//		return null;
//	}

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
public <IPT> Map<BoogieIcfgLocation, IPredicate> generateInvariantsForTransitions(final List<BoogieIcfgLocation> locations, 
		final List<IcfgInternalAction> transitions,
		final IPredicate precondition, final IPredicate postcondition,
		final IInvariantPatternProcessorFactory<IPT> invPatternProcFactory, final boolean useVariablesFromUnsatCore, 
		final boolean useLiveVariables, final Set<IProgramVar> liveVariables) {
	final IInvariantPatternProcessor<IPT> processor = invPatternProcFactory.produce(locations, transitions, precondition,
			postcondition);

	logService.info("(Path)program has " + locations.size() + " locations");
	final Map<BoogieIcfgLocation, IPT> patterns = new HashMap<BoogieIcfgLocation, IPT>(locations.size());
	final Collection<InvariantTransitionPredicate<IPT>> predicates = new ArrayList<InvariantTransitionPredicate<IPT>>(
			transitions.size() + 2);
	
	Map<TermVariable, IProgramVar> smtVars2ProgramVars = new HashMap<>();
	if (useVariablesFromUnsatCore) {
		// Compute map smt-variables to program variables
		for (IcfgInternalAction t : transitions) {
			// Add value-key-pairs from transitions invars to smtVars2ProgramVars
			for (Map.Entry<IProgramVar, TermVariable> entry : t.getTransformula().getInVars().entrySet()) {
				smtVars2ProgramVars.put(entry.getValue(), entry.getKey());
			}
			// Add value-key-pairs from transitions outvars to smtVars2ProgramVars
			for (Map.Entry<IProgramVar, TermVariable> entry : t.getTransformula().getOutVars().entrySet()) {
				smtVars2ProgramVars.put(entry.getValue(), entry.getKey());
			}
		}
	}
	
	Set<IProgramVar> varsFromUnsatCore = null;

	for (int round = 0; round < processor.getMaxRounds(); round++) {
		// Die if we run into timeouts or are otherwise requested to cancel.
		if (!pmService.continueProcessing()) {
			throw new ToolchainCanceledException(CFGInvariantsGenerator.class);
		}

		// Start round
		processor.startRound(round, useLiveVariables, liveVariables, useVariablesFromUnsatCore, varsFromUnsatCore);
		logService.info("[CFGInvariants] Round " + round + " started");

		// Build pattern map
		patterns.clear();
		for (final BoogieIcfgLocation location : locations) {
			patterns.put(location, processor.getInvariantPatternForLocation(location, round));
		}
		logService.info("[CFGInvariants] Built pattern map.");

		// Build transition predicates
		predicates.clear();
		for (final IcfgInternalAction transition : transitions) {
			final IPT invStart = patterns.get(transition.getSource());
			final IPT invEnd = patterns.get(transition.getTarget());
			predicates.add(new InvariantTransitionPredicate<IPT>(invStart, invEnd, transition.getTransformula()));
		}
		logService.info("[CFGInvariants] Built " + predicates.size() + " predicates.");

		// Attempt to find a valid configuration
		if (processor.hasValidConfiguration(predicates, round)) {
			logService.info("[CFGInvariants] Found valid " + "configuration in round " + round + ".");

			final Map<BoogieIcfgLocation, IPredicate> result = new HashMap<BoogieIcfgLocation, IPredicate>(
					locations.size());
			for (final BoogieIcfgLocation location : locations) {
				result.put(location, processor.applyConfiguration(patterns.get(location)));
			}
			return result;
		} else {
			// If no configuration could have been found, the constraints may be unsatisfiable
			if (useVariablesFromUnsatCore) {
				Collection<TermVariable> smtVarsFromUnsatCore = ((LinearInequalityInvariantPatternProcessor)processor).getVarsFromUnsatCore();
				if (smtVarsFromUnsatCore != null) {
					// The result in pattern processor was 'unsat'
					varsFromUnsatCore = new HashSet<>(smtVarsFromUnsatCore.size());
					for (TermVariable smtVar : smtVarsFromUnsatCore) {
						varsFromUnsatCore.add(smtVars2ProgramVars.get(smtVar));
					}
				} else {
					// The result in pattern processor was 'unknown', so reset varsFromUnsatCore to null
					varsFromUnsatCore = null;
				}
			}
		}
	}

	logService.info(
			"[CFGInvariants] No valid configuration " + "within round bound (" + processor.getMaxRounds() + ").");
	return null;
}
}
