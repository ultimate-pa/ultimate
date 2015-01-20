package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;

/**
 * Uses Craig interpolation for computation of nested interpolants.
 * Supports two algorithms.
 * 1. Matthias' recursive algorithm.
 * 2. Tree interpolation
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */
public class InterpolatingTraceCheckerCraig extends InterpolatingTraceChecker {


	/**
	 * Check if trace fulfills specification given by precondition,
	 * postcondition and pending contexts. The pendingContext maps the positions
	 * of pending returns to predicates which define possible variable
	 * valuations in the context to which the return leads the trace.
	 * 
	 * @param assertCodeBlocksIncrementally
	 *            If set to false, check-sat is called after all CodeBlocks are
	 *            asserted. If set to true we use Betims heuristic an
	 *            incrementally assert CodeBlocks and do check-sat until all
	 *            CodeBlocks are asserted or the result to a check-sat is UNSAT.
	 * @param logger
	 * @param services
	 * @param predicateUnifier 
	 * @param interpolation 
	 */
	public InterpolatingTraceCheckerCraig(IPredicate precondition, IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts, NestedWord<CodeBlock> trace, SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals, AssertCodeBlockOrder assertCodeBlocksIncrementally,
			IUltimateServiceProvider services, boolean computeRcfgProgramExecution, 
			PredicateUnifier predicateUnifier, INTERPOLATION interpolation) {
		super(precondition, postcondition, pendingContexts, trace, smtManager, modifiedGlobals,
				assertCodeBlocksIncrementally, services, computeRcfgProgramExecution, predicateUnifier);
		if (isCorrect() == LBool.UNSAT) {
			computeInterpolants(new AllIntegers(), interpolation);
		}
	}




//	protected int[] getSizeOfPredicates(INTERPOLATION interpolation) {
//		return m_SmtManager.computeDagSizeOfPredicates(m_Interpolants);
//	}

	/**
	 * 
	 * @param interpolation
	 * @return
	 */
	protected int getTotalNumberOfPredicates(INTERPOLATION interpolation) {
		return m_Interpolants != null ? m_Interpolants.length : 0;
	}


	@Override
	protected void computeInterpolants(Set<Integer> interpolatedPositions,
			INTERPOLATION interpolation) {
		m_TraceCheckerBenchmarkGenerator.start(TraceCheckerBenchmarkType.s_InterpolantComputation);
		assert m_PredicateUnifier != null;
		assert m_PredicateUnifier.isRepresentative(m_Precondition);
		assert m_PredicateUnifier.isRepresentative(m_Postcondition);
		for (IPredicate pred : m_PendingContexts.values()) {
			assert m_PredicateUnifier.isRepresentative(pred);
		}
		switch (interpolation) {
		case Craig_NestedInterpolation:
			computeInterpolants_Recursive(interpolatedPositions);
			break;
		case Craig_TreeInterpolation:
			computeInterpolants_Tree(interpolatedPositions);
			break;
		default:
			throw new UnsupportedOperationException("unsupportedInterpolation");
		}
		m_TraceCheckFinished = true;

		m_TraceCheckerBenchmarkGenerator.stop(TraceCheckerBenchmarkType.s_InterpolantComputation);
		// TODO: remove this if relevant variables are definitely correct.
		// assert testRelevantVars() : "bug in relevant varialbes";
	}

	private boolean testRelevantVars() {
		boolean result = true;
		RelevantVariables rv = new RelevantVariables(m_DefaultTransFormulas, m_ModifiedGlobals);
		for (int i = 0; i < m_Interpolants.length; i++) {
			IPredicate itp = m_Interpolants[i];
			Set<BoogieVar> vars = itp.getVars();
			Set<BoogieVar> frel = rv.getForwardRelevantVariables()[i + 1];
			Set<BoogieVar> brel = rv.getBackwardRelevantVariables()[i + 1];
			if (!frel.containsAll(vars)) {
				mLogger.warn("forward relevant variables wrong");
				result = false;
			}
			if (!brel.containsAll(vars)) {
				mLogger.warn("backward relevant variables wrong");
				result = false;
			}
		}
		return result;
	}

	public IPredicate[] getInterpolants() {
		if (isCorrect() == LBool.UNSAT) {
			if (m_Interpolants == null) {
				throw new AssertionError("No Interpolants");
			}
			assert m_Interpolants.length == m_Trace.length() - 1;
			return m_Interpolants;
		} else {
			throw new UnsupportedOperationException("Interpolants are only available if trace is correct.");
		}
	}


	/**
	 * Use tree interpolants to compute nested interpolants.
	 */
	private void computeInterpolants_Tree(Set<Integer> interpolatedPositions) {
		if (m_IsSafe != LBool.UNSAT) {
			throw new IllegalArgumentException("Interpolants only available if trace fulfills specification");
		}
		if (m_Interpolants != null) {
			throw new AssertionError("You already computed interpolants");
		}
		NestedInterpolantsBuilder nib = new NestedInterpolantsBuilder(m_SmtManager, m_AAA.getAnnotatedSsa(),
				m_Nsb.getConstants2BoogieVar(), m_PredicateUnifier, interpolatedPositions, true, mLogger, this);
		m_Interpolants = nib.getNestedInterpolants();
		assert !inductivityOfSequenceCanBeRefuted();
		assert m_Interpolants != null;
	}

	/**
	 * Use Matthias' old naive iterative method to compute nested interpolants.
	 * (Recursive interpolation queries, one for each call-return pair)
	 */
	private void computeInterpolants_Recursive(Set<Integer> interpolatedPositions) {
		assert interpolatedPositions != null : "no interpolatedPositions";
		if (m_IsSafe != LBool.UNSAT) {
			if (m_IsSafe == null) {
				throw new AssertionError("No trace check at the moment - no interpolants!");
			} else {
				throw new AssertionError("Interpolants only available if trace fulfills specification");
			}
		}
		if (m_Interpolants != null) {
			throw new AssertionError("You already computed interpolants");
		}

		List<Integer> nonPendingCallPositions = new ArrayList<Integer>();
		Set<Integer> newInterpolatedPositions = interpolatedPositionsForSubtraces(interpolatedPositions,
				nonPendingCallPositions);

		NestedInterpolantsBuilder nib = new NestedInterpolantsBuilder(m_SmtManager, m_AAA.getAnnotatedSsa(),
				m_Nsb.getConstants2BoogieVar(), m_PredicateUnifier, newInterpolatedPositions, false, mLogger, this);
		m_Interpolants = nib.getNestedInterpolants();
		IPredicate oldPrecondition = m_Precondition;
		IPredicate oldPostcondition = m_Postcondition;

		// forget trace - endTraceCheck already called
		if (m_Interpolants != null) {
			assert !inductivityOfSequenceCanBeRefuted();
		}

		for (Integer nonPendingCall : nonPendingCallPositions) {
			// compute subtrace from to call to corresponding return
			int returnPosition = m_Trace.getReturnPosition(nonPendingCall);
			NestedWord<CodeBlock> subtrace = m_Trace.getSubWord(nonPendingCall + 1, returnPosition);

			Call call = (Call) m_Trace.getSymbol(nonPendingCall);
			String calledMethod = call.getCallStatement().getMethodName();
			TermVarsProc oldVarsEquality = m_SmtManager.getOldVarsEquality(calledMethod, m_ModifiedGlobals);

			IPredicate precondition = m_PredicateUnifier.getOrConstructPredicate(oldVarsEquality);

			// Use a pendingContext the interpolant at the position before the
			// call, if this is -1 (because call is first codeBlock) use the
			// precondition used in this recursive interpolant computation one
			// level above
			SortedMap<Integer, IPredicate> pendingContexts = new TreeMap<Integer, IPredicate>();
			IPredicate beforeCall;
			if (nonPendingCall == 0) {
				beforeCall = oldPrecondition;
			} else {
				beforeCall = m_Interpolants[nonPendingCall - 1];
			}
			pendingContexts.put(subtrace.length() - 1, beforeCall);

			// Check if subtrace is "compatible" with interpolants computed so
			// far. Obviously trace fulfills specification, but we need this
			// proof to be able to compute interpolants.
			IPredicate interpolantAtReturnPosition;
			if (returnPosition == m_Trace.length() - 1) {
				// special case: last position of trace is return
				// interpolant at this position is the postcondition
				// (which is stored in oldPostcondition, since m_Postcondition
				// is already set to null.
				interpolantAtReturnPosition = oldPostcondition;
				assert interpolantAtReturnPosition != null;
			} else {
				interpolantAtReturnPosition = m_Interpolants[returnPosition];
				assert interpolantAtReturnPosition != null;
			}
			
			// Compute interpolants for subsequence and add them to interpolants
			// computed by this TraceChecker
			InterpolatingTraceCheckerCraig tc = new InterpolatingTraceCheckerCraig(precondition, interpolantAtReturnPosition, pendingContexts, subtrace,
					m_SmtManager, m_ModifiedGlobals, m_assertCodeBlocksIncrementally, mServices, false, m_PredicateUnifier, INTERPOLATION.Craig_NestedInterpolation);
			LBool isSafe = tc.isCorrect();
			if (isSafe != LBool.UNSAT) {
				throw new AssertionError("has to be unsat by construction, we do check only for interpolant computation");
			}
			// tc.computeInterpolants_Recursive(interpolatedPositions, m_PredicateUnifier);
			IPredicate[] interpolantSubsequence = tc.getInterpolants();

			assert m_SmtManager.isDontCare(m_Interpolants[nonPendingCall]);
			m_Interpolants[nonPendingCall] = precondition;
			for (int i = 0; i < interpolantSubsequence.length; i++) {
				assert m_SmtManager.isDontCare(m_Interpolants[nonPendingCall + 1 + i]);
				m_Interpolants[nonPendingCall + 1 + i] = interpolantSubsequence[i];
			}
		}
	}

	/**
	 * Compute interpolated positions used in recursive interpolant computation
	 */
	private Set<Integer> interpolatedPositionsForSubtraces(Set<Integer> interpolatedPositions,
			List<Integer> nonPendingCallPositions) {

		Set<Integer> newInterpolatedPositions = new HashSet<Integer>();

		int currentContextStackDepth = 0;
		NestedWord<CodeBlock> nestedTrace = (NestedWord<CodeBlock>) m_Trace;
		for (int i = 0; i < nestedTrace.length() - 1; i++) {

			if (nestedTrace.isInternalPosition(i)) {
				if (interpolatedPositions.contains(i) && currentContextStackDepth == 0) {
					newInterpolatedPositions.add(i);
				}
			} else if (nestedTrace.isCallPosition(i)) {
				if (nestedTrace.isPendingCall(i)) {
					if (interpolatedPositions.contains(i) && currentContextStackDepth == 0) {
						newInterpolatedPositions.add(i);
					}
				} else {
					// we need interpolant before call if
					// currentContextStackDepth == 0
					if (currentContextStackDepth == 0) {
						nonPendingCallPositions.add(i);
					}
					currentContextStackDepth++;
					assert currentContextStackDepth > 0;
				}
			} else if (nestedTrace.isReturnPosition(i)) {
				currentContextStackDepth--;
				// new need interpolant after return if currentContextStackDepth
				// == 0
				if (currentContextStackDepth == 0) {
					newInterpolatedPositions.add(i);
				}
			} else {
				throw new AssertionError();
			}
		}
		return newInterpolatedPositions;
	}

}