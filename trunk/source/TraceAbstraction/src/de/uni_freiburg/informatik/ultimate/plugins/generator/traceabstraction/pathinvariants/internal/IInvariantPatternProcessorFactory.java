package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

/**
 * A factory producing {@link IInvariantPatternProcessor}s.
 */
public interface IInvariantPatternProcessorFactory {

	/**
	 * Produces a new {@link IInvariantPatternProcessor} instance for a given
	 * {@link ControlFlowGraph}.
	 * 
	 * @param cfg
	 *            the control flow graph to generate a processor for
	 * @return new {@link IInvariantPatternProcessor} instance
	 */
	public IInvariantPatternProcessor produce(final ControlFlowGraph cfg);
}
