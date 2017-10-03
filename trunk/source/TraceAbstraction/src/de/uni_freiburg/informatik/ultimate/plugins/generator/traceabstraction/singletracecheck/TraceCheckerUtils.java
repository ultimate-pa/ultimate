/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermClassifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckReasonUnknown.Reason;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ExceptionHandlingCategory;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

/**
 * Class that contains static methods that are related to the {@link TraceCheck}.
 *
 * @author Matthias Heizmann
 */
public final class TraceCheckerUtils {
	private TraceCheckerUtils() {
		// utility class
	}

	/**
	 * Given a trace cb_0,...,cb_n returns the sequence of ProgramPoints that corresponds to this trace. This is the
	 * sequence pp_0,...,pp_{n+1} such that
	 * <ul>
	 * <li>pp_i is the ProgramPoint before CodeBlock cb_i, and
	 * <li>pp_{i+1} is the ProgramPoint after CodeBlock cb_i.
	 * </ul>
	 *
	 * @param trace
	 *            trace
	 * @return sequence of program points
	 */
	public static List<IcfgLocation> getSequenceOfProgramPoints(final NestedWord<? extends IIcfgTransition<?>> trace) {
		final List<IcfgLocation> result = new ArrayList<>();
		for (final IIcfgTransition<?> cb : trace) {
			final IcfgLocation pp = cb.getSource();
			result.add(pp);
		}
		final IIcfgTransition<?> cb = trace.getSymbol(trace.length() - 1);
		final IcfgLocation pp = cb.getTarget();
		result.add(pp);
		return result;
	}

	/**
	 * Variant of
	 * {@link #computeCoverageCapability(IUltimateServiceProvider, TracePredicates, List, ILogger, PredicateUnifier)}
	 * where the sequence of ProgramPoints is not a parameter but computed from the trace.
	 *
	 * @param services
	 *            Ultimate services
	 * @param traceChecker
	 *            trace checker
	 * @param logger
	 *            logger
	 * @return backward covering information
	 */
	public static BackwardCoveringInformation computeCoverageCapability(final IUltimateServiceProvider services,
			final IInterpolantGenerator traceChecker, final ILogger logger) {
		@SuppressWarnings("unchecked")
		final NestedWord<CodeBlock> trace = (NestedWord<CodeBlock>) NestedWord.nestedWord(traceChecker.getTrace());
		final List<IcfgLocation> programPoints = getSequenceOfProgramPoints(trace);
		return computeCoverageCapability(services, traceChecker.getIpp(), programPoints, logger,
				traceChecker.getPredicateUnifier());
	}

	public static <CL> BackwardCoveringInformation computeCoverageCapability(final IUltimateServiceProvider services,
			final TracePredicates ipp, final List<CL> controlLocationSequence,
			final ILogger logger, final IPredicateUnifier predicateUnifier) {
		final CoverageAnalysis<CL> ca =
				new CoverageAnalysis<>(services, ipp, controlLocationSequence, logger, predicateUnifier);
		ca.analyze();
		return ca.getBackwardCoveringInformation();
	}

	/***
	 * Checks whether the given sequence of predicates is inductive. For each i we check if {predicates[i-1]} st_i
	 * {predicates[i]} is a valid Hoare triple. If all triples are valid, we return true. Otherwise an exception is
	 * thrown.
	 *
	 * @param interpolants
	 *            sequence of interpolants
	 * @param trace
	 *            trace
	 * @param precondition
	 *            precondition
	 * @param postcondition
	 *            postcondition
	 * @param pendingContexts
	 *            pending contexts
	 * @param computation
	 *            computation string
	 * @param csToolkit
	 *            CFG-SMT toolkit
	 * @param logger
	 *            logger
	 * @param managedScript
	 *            managed script
	 * @return {@code true}
	 */
	public static boolean checkInterpolantsInductivityForward(final List<IPredicate> interpolants,
			final NestedWord<? extends IAction> trace, final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final String computation,
			final CfgSmtToolkit csToolkit, final ILogger logger, final ManagedScript managedScript) {
		final IHoareTripleChecker htc = new MonolithicHoareTripleChecker(csToolkit);
		final TracePredicates ipp =
				new TracePredicates(precondition, postcondition, interpolants);
		Validity result;
		for (int i = 0; i <= interpolants.size(); i++) {
			result = checkInductivityAtPosition(i, ipp, trace, pendingContexts, htc, logger);
			if (result != Validity.VALID && result != Validity.UNKNOWN) {
				throw new AssertionError("invalid Hoare triple in " + computation);
			}
		}
		return true;
	}

	/***
	 * Similar to the method
	 * {@link #checkInterpolantsInductivityForward(List, NestedWord, IPredicate, IPredicate, SortedMap, String, CfgSmtToolkit, ILogger, ManagedScript)}
	 * . But here we start from the end. This ensures that we get the last Hoare triple that is invalid.
	 *
	 * @param interpolants
	 *            sequence of interpolants
	 * @param trace
	 *            trace
	 * @param precondition
	 *            precondition
	 * @param postcondition
	 *            postcondition
	 * @param pendingContexts
	 *            pending contexts
	 * @param computation
	 *            computation string
	 * @param csToolkit
	 *            CFG-SMT toolkit
	 * @param logger
	 *            logger
	 * @param managedScript
	 *            managed script
	 * @return {@code true}
	 */
	public static boolean checkInterpolantsInductivityBackward(final List<IPredicate> interpolants,
			final NestedWord<? extends IAction> trace, final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final String computation,
			final CfgSmtToolkit csToolkit, final ILogger logger, final ManagedScript managedScript) {
		final IHoareTripleChecker htc = new MonolithicHoareTripleChecker(csToolkit);
		final TracePredicates ipp =
				new TracePredicates(precondition, postcondition, interpolants);
		for (int i = interpolants.size(); i >= 0; i--) {
			final Validity result;
			result = checkInductivityAtPosition(i, ipp, trace, pendingContexts, htc, logger);
			if (result != Validity.VALID && result != Validity.UNKNOWN) {
				throw new AssertionError("invalid Hoare triple in " + computation);
			}
		}
		return true;
	}

	private static Validity checkInductivityAtPosition(final int pos, final TracePredicates ipp,
			final NestedWord<? extends IAction> trace, final SortedMap<Integer, IPredicate> pendingContexts,
			final IHoareTripleChecker htc, final ILogger logger) {
		final IPredicate predecessor = ipp.getPredicate(pos);
		final IPredicate successor = ipp.getPredicate(pos + 1);
		final IAction cb = trace.getSymbol(pos);
		final Validity result;
		if (trace.isCallPosition(pos)) {
			assert cb instanceof ICallAction : "not Call at call position";
			result = htc.checkCall(predecessor, (ICallAction) cb, successor);
			logger.info(new DebugMessage("{0}: Hoare triple '{'{1}'}' {2} '{'{3}'}' is {4}", pos, predecessor, cb,
					successor, result));
		} else if (trace.isReturnPosition(pos)) {
			assert cb instanceof IReturnAction : "not Call at call position";
			IPredicate hierarchicalPredecessor;
			if (trace.isPendingReturn(pos)) {
				hierarchicalPredecessor = pendingContexts.get(pos);
			} else {
				final int callPosition = trace.getCallPosition(pos);
				hierarchicalPredecessor = ipp.getPredicate(callPosition);
			}
			result = htc.checkReturn(predecessor, hierarchicalPredecessor, (IReturnAction) cb, successor);
			logger.info(new DebugMessage("{0}: Hoare quadruple '{'{1}'}' '{'{5}'}' {2} '{'{3}'}' is {4}", pos,
					predecessor, cb, successor, result, hierarchicalPredecessor));
		} else if (trace.isInternalPosition(pos)) {
			assert cb instanceof IInternalAction;
			result = htc.checkInternal(predecessor, (IInternalAction) cb, successor);
			logger.info(new DebugMessage("{0}: Hoare triple '{'{1}'}' {2} '{'{3}'}' is {4}", pos, predecessor, cb,
					successor, result));
		} else {
			throw new AssertionError("unsupported position");
		}
		return result;
	}

	/**
	 * Compute some program execution for this trace (due to large block encoding there might be several). The resulting
	 * program execution does not provide any values. This is needed e.g., in case the solver said UNKNOWN while
	 * analyzing a trace.
	 */
	public static IcfgProgramExecution
			computeSomeIcfgProgramExecutionWithoutValues(final Word<? extends IIcfgTransition<?>> trace) {
		@SuppressWarnings("unchecked")
		final Map<TermVariable, Boolean>[] branchEncoders = new Map[0];
		return new IcfgProgramExecution(trace.asList(), Collections.emptyMap(), branchEncoders);
	}
	
	
	/**
	 * Use {@link TermClassifier} to classify set of {@link Term}s that belong
	 * to a trace, and return the {@link TermClassifier}.
	 * TODO: Maybe also check local vars assignment and global vars assignment?
	 */
	public static TermClassifier classifyTermsInTrace(final Word<? extends IAction> word,
			final IPredicate axioms) {

		final TermClassifier cs = new TermClassifier();
		cs.checkTerm(axioms.getFormula());
		for (final IAction action : word) {
			if (action instanceof IInternalAction) {
				cs.checkTerm(((IInternalAction) action).getTransformula().getFormula());
			} else if (action instanceof ICallAction) {
				cs.checkTerm(((ICallAction) action).getLocalVarsAssignment().getFormula());
			} else if (action instanceof IReturnAction) {
				cs.checkTerm(((IReturnAction) action).getAssignmentOfReturn().getFormula());
			}
		}
		return cs;
	}
	
	public static final String SMTINTERPOL_NONLINEAR_ARITHMETIC_MESSAGE = "Unsupported non-linear arithmetic";
	public static final String CVC4_NONLINEAR_ARITHMETIC_MESSAGE_PREFIX = "A non-linear fact";
	
	
	public static TraceCheckReasonUnknown constructReasonUnknown(final SMTLIBException e) {
		final String message = e.getMessage();
		final Reason reason;
		final ExceptionHandlingCategory exceptionCategory;
		if (message == null) {
			reason = Reason.SOLVER_CRASH_OTHER;
			exceptionCategory = ExceptionHandlingCategory.UNKNOWN;
		} else if (message.equals(SMTINTERPOL_NONLINEAR_ARITHMETIC_MESSAGE)) {
			// SMTInterpol does not support non-linear arithmetic
			reason = Reason.UNSUPPORTED_NON_LINEAR_ARITHMETIC;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
		} else if (message.startsWith(CVC4_NONLINEAR_ARITHMETIC_MESSAGE_PREFIX)) {
			// CVC4 does not support nonlinear arithmetic if some LIA or LRA logic is used.
			reason = Reason.UNSUPPORTED_NON_LINEAR_ARITHMETIC;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
		} else if (message.endsWith("Connection to SMT solver broken")) {
			// broken SMT solver connection can have various reasons such as misconfiguration or solver crashes
			reason = Reason.SOLVER_CRASH_OTHER;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_DEPENDING;
		} else if (message.endsWith("Received EOF on stdin. No stderr output.")) {
			// problem with Z3
			reason = Reason.SOLVER_CRASH_OTHER;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_DEPENDING;
		} else if (message.contains("Received EOF on stdin. stderr output:")) {
			// problem with CVC4
			reason = Reason.SOLVER_CRASH_OTHER;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_THROW;
		} else if (message.startsWith("Logic does not allow numerals")) {
			// wrong usage of external solver, tell the user
			reason = Reason.SOLVER_CRASH_WRONG_USAGE;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
		} else if (message.startsWith("Timeout exceeded")) {
			// timeout
			reason = Reason.SOLVER_RESPONSE_TIMEOUT;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
		} else if (message.startsWith("ERROR: bvadd takes exactly 2 arguments")) {
			// we use bvadd with larger number of params, e.g., MatSAT complains
			reason = Reason.ULTIMATE_VIOLATES_SMT_LIB_STANDARD_AND_SOLVER_COMPLAINS;
			exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
		} else {
			reason = Reason.SOLVER_CRASH_OTHER;
			exceptionCategory = ExceptionHandlingCategory.UNKNOWN;
		}
		return new TraceCheckReasonUnknown(reason, e, exceptionCategory);
	}
}
