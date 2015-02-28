package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * A generator for a map of invariants to {@link ControlFlowGraph.Location}s
 * within a {@link ControlFlowGraph}, using a {@link IInvariantPatternProcessor}
 * .
 */
public final class CFGInvariantsGenerator {

	private final ILoggingService logService;
	private final PredicateUnifier predicateUnifier;
	private final SmtManager smtManager;
	private final ModifiableGlobalVariableManager modGlobVarManager;

	/**
	 * Create a generator for invariant maps on {@link ControlFlowGraph}s.
	 * 
	 * @param logService
	 *            service to use for logging
	 * @param predicateUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param smtManager
	 *            manager to access SMT stuff(TM) TODO
	 * @param modGlobVarManager
	 *            ??? TODO
	 */
	public CFGInvariantsGenerator(final ILoggingService logService,
			final PredicateUnifier predicateUnifier,
			final SmtManager smtManager,
			final ModifiableGlobalVariableManager modGlobVarManager) {
		this.logService = logService;
		this.predicateUnifier = predicateUnifier;
		this.smtManager = smtManager;
		this.modGlobVarManager = modGlobVarManager;
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
	public Map<ControlFlowGraph.Location, IPredicate> generateInvariantsFromCFG(
			final ControlFlowGraph cfg, final IPredicate precondition,
			final IPredicate postcondition,
			final IInvariantPatternProcessorFactory invPatternProcFactory) {
		final IInvariantPatternProcessor processor = invPatternProcFactory
				.produce(cfg);

		throw new UnsupportedOperationException("not yet implemented");
	}
}
