package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceChecker;

/**
 * An {@link IRefinementStrategy} allows an {@link IRefinementSelector} to try multiple combinations of trace checker
 * and interpolant generator.<br>
 * In the following, this combination is just called "combination".
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public interface IRefinementStrategy<T> {
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
	 * @return The interpolant generator of the current combination.
	 */
	IInterpolantGenerator getInterpolantGenerator();
	
	/**
	 * @return The interpolant automaton.
	 */
	T getInfeasibilityProof();
}
