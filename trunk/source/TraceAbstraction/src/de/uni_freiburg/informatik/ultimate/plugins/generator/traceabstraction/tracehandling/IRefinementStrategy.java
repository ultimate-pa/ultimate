package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.ArrayList;
import java.util.List;
import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.InterpolantAutomatonBuilderFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TracePredicates;

/**
 * An {@link IRefinementStrategy} allows an {@link IRefinementEngine} to try multiple combinations of
 * <ol>
 * <li>a {@link TraceCheck},</li>
 * <li>an {@link IInterpolantGenerator}, and</li>
 * <li>an {@link InterpolantAutomatonBuilderFactory}.</li>
 * </ol>
 * In the following class documentation this combination is just called "combination".
 * <p>
 * The contract is that if {@link #hasNextTraceChecker()} (resp. {@link #hasNextInterpolantGenerator(List, List)})
 * returns {@code true}, then {@link #nextTraceChecker()} (resp. {@link #nextInterpolantGenerator()}) advances the
 * respective component (but the strategy may also return {@code false} to enforce early termination).<br>
 * Between two calls to {@link #nextTraceChecker()} (resp. {@link #nextInterpolantGenerator()}) the respective getter (
 * {@link #getTraceChecker()} resp. {@link IRefinementStrategy#getInterpolantGenerator()}) always returns the same
 * object and {@link #hasNextTraceChecker()} (resp. {@link #hasNextInterpolantGenerator(List, List)}) always returns the
 * same answer. However, for instance by a call to {@link #nextInterpolantGenerator()}, the {@link TraceCheck} may
 * change. A user should hence not store these objects temporarily.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public interface IRefinementStrategy<LETTER> {
	String COMMAND_Z3_NO_TIMEOUT = "z3 -smt2 -in SMTLIB2_COMPLIANT=true";
	String COMMAND_Z3_TIMEOUT = COMMAND_Z3_NO_TIMEOUT + " -t:12000";
	String COMMAND_CVC4_NO_TIMEOUT = "cvc4 --tear-down-incremental --print-success --lang smt --rewrite-divk";
	String COMMAND_CVC4_TIMEOUT = COMMAND_CVC4_NO_TIMEOUT + " --tlimit-per=12000";
	// 20161214 Matthias: MathSAT does not support timeouts
	String COMMAND_MATHSAT = "mathsat -unsat_core_generation=3";

	long TIMEOUT_SMTINTERPOL = 12_000L;
	long TIMEOUT_NONE_SMTINTERPOL = 0L;

	String LOGIC_Z3 = "ALL";
	String LOGIC_CVC4_DEFAULT = "AUFLIRA";
	String LOGIC_CVC4_BITVECTORS = "AUFBV";
	String LOGIC_MATHSAT = "ALL";

	/**
	 * A user should use this method whenever the trace check was unsuccessful (i.e., crashed or returned
	 * {@link LBool.UNKNOWN}. The strategy then decides whether it wants to and whether it can use another
	 * {@link TraceCheck}.
	 *
	 * @return {@code true} iff there is another {@link TraceCheck} available and should be used
	 */
	boolean hasNextTraceChecker();

	/**
	 * Changes the {@link TraceCheck}.<br>
	 * Throws a {@link NoSuchElementException} if there is no next {@link TraceCheck}; use
	 * {@link #hasNextTraceChecker()} to check this.
	 */
	void nextTraceChecker();

	/**
	 * @return The trace checker of the current combination.
	 */
	TraceCheck getTraceChecker();

	/**
	 * A user should use this method whenever new interpolants have been computed (or the computation has failed). The
	 * strategy then decides whether it wants to and whether it can use another {@link IInterpolantGenerator}.
	 *
	 * @param perfectIpps
	 *            perfect interpolant sequences constructed so far
	 * @param imperfectIpps
	 *            imperfect interpolant sequences constructed so far
	 * @return {@code true} iff there is another {@link IInterpolantGenerator} available and should be used
	 */
	boolean hasNextInterpolantGenerator(List<TracePredicates> perfectIpps,
			List<TracePredicates> imperfectIpps);

	/**
	 * Changes the {@link IInterpolantGenerator}.<br>
	 * Throws a {@link NoSuchElementException} if there is no next {@link IInterpolantGenerator}; use
	 * {@link #hasNextInterpolantGenerator(List, List)} to check this.
	 */
	void nextInterpolantGenerator();

	/**
	 * This method must only be called if the {@link TraceCheck} returns {@code UNSAT}.
	 *
	 * @return The interpolant generator of the current combination.
	 */
	IInterpolantGenerator getInterpolantGenerator();

	/**
	 * @param perfectIpps
	 *            Sequences of perfect interpolants.
	 * @param imperfectIpps
	 *            sequences of imperfect interpolants
	 * @return an interpolant automaton builder
	 */
	IInterpolantAutomatonBuilder<LETTER, IPredicate> getInterpolantAutomatonBuilder(
			List<TracePredicates> perfectIpps,
			List<TracePredicates> imperfectIpps);

	/**
	 * @return Predicate unifier.
	 */
	IPredicateUnifier getPredicateUnifier();

	/**
	 * @return Object that encapsulates which exceptions are blacklisted.
	 * @see RefinementStrategyExceptionBlacklist
	 */
	RefinementStrategyExceptionBlacklist getExceptionBlacklist();
	
	
	RefinementEngineStatisticsGenerator getRefinementEngineStatistics();

	/**
	 * @param list1
	 *            First list.
	 * @param list2
	 *            second list
	 * @return new list containing all elements from the two lists
	 */
	static List<TracePredicates> wrapTwoListsInOne(
			final List<TracePredicates> list1,
			final List<TracePredicates> list2) {
		final List<TracePredicates> allIpps = new ArrayList<>(list1.size() + list2.size());
		allIpps.addAll(list1);
		allIpps.addAll(list2);
		return allIpps;
	}
}
