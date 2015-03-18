package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Location;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Transition;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * A generator for a map of invariants to {@link ControlFlowGraph.Location}s
 * within a {@link ControlFlowGraph}, using a {@link IInvariantPatternProcessor}
 * .
 */
public final class CFGInvariantsGenerator {
	
	private final Logger logService;
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
		this.pmService = services.getProgressMonitorService();
		this.logService = services.getLoggingService().getLogger(
				Activator.s_PLUGIN_ID);
	}

	/**
	 * Attempts to generate an invariant map on a given {@link ControlFlowGraph}
	 * using a {@link IInvariantPatternProcessor} from the given
	 * {@link IInvariantPatternProcessorFactory}.
	 * 
	 * The {@link IInvariantPatternProcessor} will be used for up to
	 * {@link IInvariantPatternProcessor#getMaxRounds()} attempts to generate
	 * such an invariant map. If all attempts fail, this method returns null.
	 * 
	 * @param <IPT>
	 *            Invariant Pattern Type: Type used for invariant patterns
	 * @param cfg
	 *            the ControlFlowGraph to generate an invariant map on
	 * @param precondition
	 *            the invariant on the {@link ControlFlowGraph#getEntry()} of
	 *            cfg
	 * @param postcondition
	 *            the invariant on the {@link ControlFlowGraph#getExit()} of cfg
	 * @param invPatternProcFactory
	 *            the factory to produce the {@link IInvariantPatternProcessor}
	 *            with
	 * @return the invariant map for the locations of cfg or null if the
	 *         processor failed to process its invariant patterns up to its
	 *         final run.
	 */
	public <IPT> Map<Location, IPredicate> generateInvariantsFromCFG(
			final ControlFlowGraph cfg, final IPredicate precondition,
			final IPredicate postcondition,
			final IInvariantPatternProcessorFactory<IPT> invPatternProcFactory) {
		final IInvariantPatternProcessor<IPT> processor = invPatternProcFactory
				.produce(cfg, precondition, postcondition);

		final Collection<Location> locations = cfg.getLocations();
		final Map<Location, IPT> patterns = new HashMap<Location, IPT>(
				locations.size());
		final Collection<Transition> transitions = cfg.getTransitions();
		final Collection<InvariantTransitionPredicate<IPT>> predicates =
				new ArrayList<InvariantTransitionPredicate<IPT>>(
						transitions.size() + 2);

		for (int round = 0; round < processor.getMaxRounds(); round++) {
			// Die if we run into timeouts or are otherwise requested to cancel.
			if (!pmService.continueProcessing()) {
				throw new ToolchainCanceledException(
						CFGInvariantsGenerator.class);
			}
			
			// Start round
			processor.startRound(round);
			logService.log(Level.INFO, "[CFGInvariants] Round " + round
					+ " started");

			// Build pattern map
			patterns.clear();
			for (final Location location : locations) {
				patterns.put(location, processor
						.getInvariantPatternForLocation(location, round));
			}
			logService.log(Level.INFO, "[CFGInvariants] Built pattern map.");

			// Build transition predicates
			predicates.clear();
			for (final Transition transition : transitions) {
				final IPT invStart = patterns.get(transition.getStart());
				final IPT invEnd = patterns.get(transition.getEnd());
				predicates.add(new InvariantTransitionPredicate<IPT>(invStart,
						invEnd, transition.getTransFormula()));
			}
			logService.log(Level.INFO,
					"[CFGInvariants] Built " + predicates.size()
							+ " predicates.");

			// Attempt to find a valid configuration
			if (processor.hasValidConfiguration(predicates, round)) {
				logService.log(Level.INFO, "[CFGInvariants] Found valid "
						+ "configuration in round " + round + ".");

				final Map<Location, IPredicate> result =
						new HashMap<ControlFlowGraph.Location, IPredicate>(
								locations.size());
				for (final Location location : locations) {
					result.put(location, processor.applyConfiguration(patterns
							.get(location)));
				}
				return result;
			}
		}

		logService.log(Level.INFO, "[CFGInvariants] No valid configuration "
				+ "within round bound (" + processor.getMaxRounds() + ").");
		return null;
	}
}
