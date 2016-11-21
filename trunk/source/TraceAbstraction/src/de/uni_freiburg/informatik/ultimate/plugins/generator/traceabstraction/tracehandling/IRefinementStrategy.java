package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.InterpolantAutomatonBuilderFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceChecker;

/**
 * An {@link IRefinementStrategy} allows an {@link IRefinementSelector} to try multiple combinations of
 * <ol>
 * <li>a {@link TraceChecker},</li>
 * <li>an {@link IInterpolantGenerator}, and</li>
 * <li>an {@link InterpolantAutomatonBuilderFactory}.</li>
 * </ol>
 * In the following, this combination is just called "combination".
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public interface IRefinementStrategy {
	/**
	 * @return {@code true} iff there are more combinations available.
	 */
	boolean hasNext();
	
	/**
	 * Changes the combination.<br>
	 * Throws a {@link NoSuchElementException} if there is no next combination; use {@link #hasNext()} to
	 * check this.
	 * <p>
	 * TODO We need an interface to give more information to the strategy about why we need a different combination.<br>
	 * We need to collect the use cases first.
	 */
	void next();
	
	/**
	 * @return The trace checker strategy of the current combination.
	 */
	TraceChecker getTraceChecker();
	
	/**
	 * This method must only be called if the {@link TraceChecker} returns {@code UNSAT}.
	 * 
	 * @return The interpolant generator of the current combination.
	 */
	IInterpolantGenerator getInterpolantGenerator();
	
	/**
	 * @return The interpolant automaton builder.
	 */
	IInterpolantAutomatonBuilder<CodeBlock, IPredicate> getInterpolantAutomatonBuilder();
}
