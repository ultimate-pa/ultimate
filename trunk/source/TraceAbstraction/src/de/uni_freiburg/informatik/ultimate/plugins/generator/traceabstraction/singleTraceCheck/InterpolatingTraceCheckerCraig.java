/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * Uses Craig interpolation for computation of nested interpolants.
 * Supports two algorithms.
 * 1. Matthias' recursive algorithm.
 * 2. Tree interpolation
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */
public class InterpolatingTraceCheckerCraig extends InterpolatingTraceChecker {

	private final boolean mInstantiateArrayExt;
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
	 * @param instanticateArrayExt 
	 */
	public InterpolatingTraceCheckerCraig(final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final NestedWord<? extends IAction> trace, final SmtManager smtManager,
			final ModifiableGlobalVariableManager modifiedGlobals, final AssertCodeBlockOrder assertCodeBlocksIncrementally,
			final IUltimateServiceProvider services, final boolean computeRcfgProgramExecution, 
			final PredicateUnifier predicateUnifier, final InterpolationTechnique interpolation, final SmtManager tcSmtManager, final boolean instanticateArrayExt,
			final XnfConversionTechnique xnfConversionTechnique, final SimplificationTechnique simplificationTechnique) {
		super(precondition, postcondition, pendingContexts, trace, smtManager, modifiedGlobals,
				assertCodeBlocksIncrementally, services, computeRcfgProgramExecution, predicateUnifier, tcSmtManager, simplificationTechnique, xnfConversionTechnique);
		mInstantiateArrayExt = instanticateArrayExt;
		if (isCorrect() == LBool.UNSAT) {
			computeInterpolants(new AllIntegers(), interpolation);
		}
	}

	public InterpolatingTraceCheckerCraig(final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final NestedWord<? extends IAction> trace, final SmtManager smtManager,
			final ModifiableGlobalVariableManager modifiedGlobals, final AssertCodeBlockOrder assertCodeBlocksIncrementally,
			final IUltimateServiceProvider services, final boolean computeRcfgProgramExecution, 
			final PredicateUnifier predicateUnifier, final InterpolationTechnique interpolation, final boolean instanticateArrayExt,
			final XnfConversionTechnique xnfConversionTechnique, final SimplificationTechnique simplificationTechnique) {
		this(precondition, postcondition, pendingContexts, trace, smtManager, 
				modifiedGlobals, assertCodeBlocksIncrementally, services, computeRcfgProgramExecution, 
				predicateUnifier, interpolation, smtManager, instanticateArrayExt, xnfConversionTechnique, simplificationTechnique);
	}


//	protected int[] getSizeOfPredicates(InterpolationTechnique interpolation) {
//		return mSmtManager.computeDagSizeOfPredicates(mInterpolants);
//	}

	/**
	 * 
	 * @param interpolation
	 * @return
	 */
	protected int getTotalNumberOfPredicates(final InterpolationTechnique interpolation) {
		return mInterpolants != null ? mInterpolants.length : 0;
	}


	@Override
	protected void computeInterpolants(final Set<Integer> interpolatedPositions,
			final InterpolationTechnique interpolation) {
		mTraceCheckerBenchmarkGenerator.start(TraceCheckerBenchmarkType.s_InterpolantComputation);
		assert mPredicateUnifier != null;
		assert mPredicateUnifier.isRepresentative(mPrecondition);
		assert mPredicateUnifier.isRepresentative(mPostcondition);
		for (final IPredicate pred : mPendingContexts.values()) {
			assert mPredicateUnifier.isRepresentative(pred);
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
		mTraceCheckerBenchmarkGenerator.reportSequenceOfInterpolants(Arrays.asList(mInterpolants));
		mTraceCheckFinished = true;

		mTraceCheckerBenchmarkGenerator.stop(TraceCheckerBenchmarkType.s_InterpolantComputation);
		// TODO: remove this if relevant variables are definitely correct.
		// assert testRelevantVars() : "bug in relevant variables";
	}

	private boolean testRelevantVars() {
		boolean result = true;
		final RelevantVariables rv = new RelevantVariables(mNestedFormulas, mModifiedGlobals);
		for (int i = 0; i < mInterpolants.length; i++) {
			final IPredicate itp = mInterpolants[i];
			final Set<IProgramVar> vars = itp.getVars();
			final Set<IProgramVar> frel = rv.getForwardRelevantVariables()[i + 1];
			final Set<IProgramVar> brel = rv.getBackwardRelevantVariables()[i + 1];
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

	@Override
	public IPredicate[] getInterpolants() {
		if (isCorrect() == LBool.UNSAT) {
			if (mInterpolants == null) {
				throw new AssertionError("No Interpolants");
			}
			assert mInterpolants.length == mTrace.length() - 1;
			return mInterpolants;
		} else {
			throw new UnsupportedOperationException("Interpolants are only available if trace is correct.");
		}
	}


	/**
	 * Use tree interpolants to compute nested interpolants.
	 */
	private void computeInterpolants_Tree(final Set<Integer> interpolatedPositions) {
		if (mIsSafe != LBool.UNSAT) {
			throw new IllegalArgumentException("Interpolants only available if trace fulfills specification");
		}
		if (mInterpolants != null) {
			throw new AssertionError("You already computed interpolants");
		}
		final NestedInterpolantsBuilder nib = new NestedInterpolantsBuilder(mTcSmtManager, mAAA.getAnnotatedSsa(),
				mNsb.getConstants2BoogieVar(), mPredicateUnifier, interpolatedPositions, true, mServices, this, mSmtManager, mInstantiateArrayExt, mSimplificationTechnique, mXnfConversionTechnique);
		mInterpolants = nib.getNestedInterpolants();
		assert TraceCheckerUtils.checkInterpolantsInductivityForward(
				Arrays.asList(mInterpolants), mTrace, mPrecondition, mPostcondition, 
				mPendingContexts, "Craig", mModifiedGlobals, mLogger, 
				mManagedScript) : 
					"invalid Hoare triple in tree interpolants";
		assert mInterpolants != null;
	}

	/**
	 * Use Matthias' old naive iterative method to compute nested interpolants.
	 * (Recursive interpolation queries, one for each call-return pair)
	 */
	private void computeInterpolants_Recursive(final Set<Integer> interpolatedPositions) {
		assert interpolatedPositions != null : "no interpolatedPositions";
		if (mIsSafe != LBool.UNSAT) {
			if (mIsSafe == null) {
				throw new AssertionError("No trace check at the moment - no interpolants!");
			} else {
				throw new AssertionError("Interpolants only available if trace fulfills specification");
			}
		}
		if (mInterpolants != null) {
			throw new AssertionError("You already computed interpolants");
		}

		final List<Integer> nonPendingCallPositions = new ArrayList<Integer>();
		final Set<Integer> newInterpolatedPositions = interpolatedPositionsForSubtraces(interpolatedPositions,
				nonPendingCallPositions);

		final NestedInterpolantsBuilder nib = new NestedInterpolantsBuilder(mTcSmtManager, mAAA.getAnnotatedSsa(),
				mNsb.getConstants2BoogieVar(), mPredicateUnifier, newInterpolatedPositions, false, mServices, this, mSmtManager, mInstantiateArrayExt, mSimplificationTechnique, mXnfConversionTechnique);
		mInterpolants = nib.getNestedInterpolants();
		final IPredicate oldPrecondition = mPrecondition;
		final IPredicate oldPostcondition = mPostcondition;

		for (final Integer nonPendingCall : nonPendingCallPositions) {
			// compute subtrace from to call to corresponding return
			final int returnPosition = mTrace.getReturnPosition(nonPendingCall);
			final NestedWord<? extends IAction> subtrace = mTrace.getSubWord(nonPendingCall + 1, returnPosition);

			final Call call = (Call) mTrace.getSymbol(nonPendingCall);
			final String calledMethod = call.getCallStatement().getMethodName();
			final TermVarsProc oldVarsEquality = mSmtManager.getOldVarsEquality(calledMethod, mModifiedGlobals);

			final IPredicate precondition = mPredicateUnifier.getOrConstructPredicate(oldVarsEquality.getFormula());

			// Use a pendingContext the interpolant at the position before the
			// call, if this is -1 (because call is first codeBlock) use the
			// precondition used in this recursive interpolant computation one
			// level above
			final SortedMap<Integer, IPredicate> pendingContexts = new TreeMap<Integer, IPredicate>();
			IPredicate beforeCall;
			if (nonPendingCall == 0) {
				beforeCall = oldPrecondition;
			} else {
				beforeCall = mInterpolants[nonPendingCall - 1];
			}
			pendingContexts.put(subtrace.length() - 1, beforeCall);

			// Check if subtrace is "compatible" with interpolants computed so
			// far. Obviously trace fulfills specification, but we need this
			// proof to be able to compute interpolants.
			IPredicate interpolantAtReturnPosition;
			if (returnPosition == mTrace.length() - 1) {
				// special case: last position of trace is return
				// interpolant at this position is the postcondition
				// (which is stored in oldPostcondition, since mPostcondition
				// is already set to null.
				interpolantAtReturnPosition = oldPostcondition;
				assert interpolantAtReturnPosition != null;
			} else {
				interpolantAtReturnPosition = mInterpolants[returnPosition];
				assert interpolantAtReturnPosition != null;
			}
			
			// Compute interpolants for subsequence and add them to interpolants
			// computed by this TraceChecker
			final InterpolatingTraceCheckerCraig tc = new InterpolatingTraceCheckerCraig(precondition, interpolantAtReturnPosition, pendingContexts, subtrace,
					mSmtManager, mModifiedGlobals, massertCodeBlocksIncrementally, mServices, false, mPredicateUnifier, 
					InterpolationTechnique.Craig_NestedInterpolation, mTcSmtManager, mInstantiateArrayExt, mXnfConversionTechnique, mSimplificationTechnique);
			final LBool isSafe = tc.isCorrect();
			if (isSafe == LBool.SAT) {
				throw new AssertionError("has to be unsat by construction, we do check only for interpolant computation");
			} else if (isSafe == LBool.UNKNOWN) {
				if(mServices.getProgressMonitorService().continueProcessing()) {
					throw new AssertionError("UNKNOWN during nested interpolation. I don't know how to continue");
				} else {
					throw new ToolchainCanceledException(this.getClass(),
							"construction of nested interpolants");
				}
			}
			// tc.computeInterpolants_Recursive(interpolatedPositions, mPredicateUnifier);
			final IPredicate[] interpolantSubsequence = tc.getInterpolants();

			assert mSmtManager.getPredicateFactory().isDontCare(mInterpolants[nonPendingCall]);
			mInterpolants[nonPendingCall] = precondition;
			for (int i = 0; i < interpolantSubsequence.length; i++) {
				assert mSmtManager.getPredicateFactory().isDontCare(mInterpolants[nonPendingCall + 1 + i]);
				mInterpolants[nonPendingCall + 1 + i] = interpolantSubsequence[i];
			}
		}
		
//		if (mInterpolants != null) {
			assert TraceCheckerUtils.checkInterpolantsInductivityForward(
					Arrays.asList(mInterpolants), mTrace, mPrecondition, mPostcondition, 
					mPendingContexts, "Craig", mModifiedGlobals, mLogger,
					mManagedScript) : 
						"invalid Hoare triple in nested interpolants";
//		}
	}

	/**
	 * Compute interpolated positions used in recursive interpolant computation
	 */
	private Set<Integer> interpolatedPositionsForSubtraces(final Set<Integer> interpolatedPositions,
			final List<Integer> nonPendingCallPositions) {

		final Set<Integer> newInterpolatedPositions = new HashSet<Integer>();

		int currentContextStackDepth = 0;
		final NestedWord<CodeBlock> nestedTrace = (NestedWord<CodeBlock>) mTrace;
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
