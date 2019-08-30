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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtFunctionsAndAxioms;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.TermClassifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

/**
 * Class that contains static methods that are related to the {@link TraceCheck}.
 *
 * @author Matthias Heizmann
 */
public final class TraceCheckUtils {
	private TraceCheckUtils() {
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
	public static List<IcfgLocation> getSequenceOfProgramPoints(final NestedWord<? extends IAction> trace) {
		final List<IcfgLocation> result = new ArrayList<>();
		final Iterator<? extends IAction> iter = trace.iterator();
		while (iter.hasNext()) {
			final IAction currentAction = iter.next();
			if (!(currentAction instanceof IIcfgTransition<?>)) {
				throw new IllegalArgumentException("currentAction is no IIcfgTransition");
			}
			final IIcfgTransition<?> transition = ((IIcfgTransition<?>) currentAction);
			result.add(transition.getSource());
			if (!iter.hasNext()) {
				result.add(transition.getTarget());
			}
		}
		return result;
	}

	/**
	 * Variant of
	 * {@link #computeCoverageCapability(IUltimateServiceProvider, TracePredicates, List, ILogger, IPredicateUnifier)}
	 * where the sequence of ProgramPoints is not a parameter but computed from the trace.
	 *
	 * @param services
	 *            Ultimate services
	 * @param traceCheck
	 *            trace checker
	 * @param logger
	 *            logger
	 * @return backward covering information
	 */
	public static BackwardCoveringInformation computeCoverageCapability(final IUltimateServiceProvider services,
			final IInterpolantGenerator<?> traceCheck, final ILogger logger) {
		@SuppressWarnings("unchecked")
		final NestedWord<CodeBlock> trace = (NestedWord<CodeBlock>) toNestedWord(traceCheck.getTrace());
		final List<IcfgLocation> programPoints = getSequenceOfProgramPoints(trace);
		return computeCoverageCapability(services, traceCheck.getIpp(), programPoints, logger,
				traceCheck.getPredicateUnifier());
	}

	/**
	 * Convert a list of letters to a {@link NestedWord}.
	 */
	public static <LETTER extends IAction> NestedWord<LETTER> toNestedWord(final List<LETTER> trace) {
		final Deque<Integer> callIndices = new ArrayDeque<>();
		final int[] nestingRelation = new int[trace.size()];
		final LETTER[] word = (LETTER[]) trace.toArray(new IAction[trace.size()]);
		int i = 0;
		for (final LETTER letter : trace) {
			word[i] = letter;
			if (letter instanceof ICallAction) {
				callIndices.push(i);
				nestingRelation[i] = NestedWord.PLUS_INFINITY;
			} else if (letter instanceof IReturnAction) {
				final int lastCall = callIndices.pop();
				nestingRelation[i] = lastCall;
				nestingRelation[lastCall] = i;
			} else if (letter instanceof IInternalAction) {
				nestingRelation[i] = NestedWord.INTERNAL_POSITION;
			} else {
				throw new UnsupportedOperationException("Type of letter is unknown: " + letter.getClass());
			}
			++i;
		}
		return new NestedWord<>(word, nestingRelation);
	}

	public static <CL> BackwardCoveringInformation computeCoverageCapability(final IUltimateServiceProvider services,
			final TracePredicates ipp, final List<CL> controlLocationSequence, final ILogger logger,
			final IPredicateUnifier predicateUnifier) {
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
		final TracePredicates ipp = new TracePredicates(precondition, postcondition, interpolants);
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
		final TracePredicates ipp = new TracePredicates(precondition, postcondition, interpolants);
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
		return IcfgProgramExecution.create(trace.asList(), Collections.emptyMap(), branchEncoders);
	}

	/**
	 * Use {@link TermClassifier} to classify set of {@link Term}s that belong to a trace, and return the
	 * {@link TermClassifier}. TODO: Maybe also check local vars assignment and global vars assignment?
	 */
	public static TermClassifier classifyTermsInTrace(final Word<? extends IAction> word, final SmtFunctionsAndAxioms smtSymbols) {

		final TermClassifier cs = new TermClassifier();
		smtSymbols.classify(cs);
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
}
