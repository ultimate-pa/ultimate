package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * A factory producing {@link IInvariantPatternProcessor}s.
 * 
 * @param <IPT>
 *            Invariant Pattern Type: Type used for invariant patterns
 */
public interface IInvariantPatternProcessorFactory<IPT> {

	/**
	 * Produces a new {@link IInvariantPatternProcessor} instance for a given
	 * {@link ControlFlowGraph}.
	 * 
	 * @param cfg
	 *            the control flow graph to generate a processor for
	 * @param precondition
	 *            the invariant on the {@link ControlFlowGraph#getEntry()} of
	 *            cfg
	 * @param postcondition
	 *            the invariant on the {@link ControlFlowGraph#getExit()} of cfg
	 * 
	 * @return new {@link IInvariantPatternProcessor} instance
	 */
	public IInvariantPatternProcessor<IPT> produce(final ControlFlowGraph cfg,
			final IPredicate precondition, final IPredicate postcondition);
}
