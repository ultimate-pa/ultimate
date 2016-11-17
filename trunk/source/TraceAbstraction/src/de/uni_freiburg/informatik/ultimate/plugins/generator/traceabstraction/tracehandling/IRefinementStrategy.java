package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceChecker;

/**
 * A {@link IRefinementStrategy} allows an {@link IRefinementSelector} to try multiple combinations of trace checker and
 * interpolant generator.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IRefinementStrategy {

	boolean hasMoreStrategies();

	void next();

	TraceChecker getTraceChecker();

	IInterpolantGenerator getInterpolantGenerator();

}