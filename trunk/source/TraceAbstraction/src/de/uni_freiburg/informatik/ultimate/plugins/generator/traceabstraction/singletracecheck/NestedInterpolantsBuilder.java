/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierSequence;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheck.TraceCheckLock;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.ConstantTermNormalizer;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

public class NestedInterpolantsBuilder {

	// TODO 2017-10-13 Matthias: When Jochen implement support for "@diff" this
	// probably has to become a parameter for this class.
	private static final boolean ALLOW_AT_DIFF = SolverBuilder.USE_DIFF_WRAPPER_SCRIPT;
	public static final String DIFF_IS_UNSUPPORTED = "@diff is unsupported";
	private static final boolean IGNORE_PQE_ERROR = false;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	private final ManagedScript mMgdScriptTc;
	private final TraceCheckLock mScriptLockOwner;
	private final ManagedScript mMgdScriptCfg;

	Term[] mCraigInterpolants;
	final PrintWriter mIterationPW = null;
	// final int mIteration =-1;
	// int mInterpolationProblem = 0;

	private final IPredicate[] mInterpolants;

	// private TAPreferences mPref = null;

	private final NestedFormulas<Term, Term> mAnnotSSA;

	private final IPredicateUnifier mPredicateUnifier;
	private final PredicateFactory mPredicateFactory;

	private final Set<Integer> mInterpolatedPositions;

	private ArrayList<Term> mInterpolInput;

	private ArrayList<Integer> mTreeStructure;

	private ArrayList<Integer> mCraigInt2interpolantIndex;

	private int mStartOfCurrentSubtree;

	private final NestedWord<? extends IAction> mTrace;

	private int mStackHeightAtLastInterpolatedPosition;

	private Stack<Integer> mStartOfSubtreeStack;

	private final boolean mTreeInterpolation;

	private final TermTransformer mConst2RepTvSubst;

	private final boolean mInstantiateArrayExt;

	public NestedInterpolantsBuilder(final ManagedScript mgdScriptTc, final TraceCheckLock scriptLockOwner,
			final NestedFormulas<Term, Term> annotatdSsa, final Map<Term, IProgramVar> constants2BoogieVar,
			final IPredicateUnifier predicateBuilder, final PredicateFactory predicateFactory,
			final Set<Integer> interpolatedPositions, final boolean treeInterpolation,
			final IUltimateServiceProvider services, final TraceCheck<? extends IAction> traceCheck,
			final ManagedScript mgdScriptCfg, final boolean instantiateArrayExt,
			final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mTreeInterpolation = treeInterpolation;
		mMgdScriptTc = mgdScriptTc;
		mScriptLockOwner = scriptLockOwner;
		mMgdScriptCfg = mgdScriptCfg;
		mPredicateUnifier = predicateBuilder;
		mPredicateFactory = predicateFactory;
		mAnnotSSA = annotatdSsa;
		mCraigInterpolants = new Term[mAnnotSSA.getTrace().length() - 1];
		mInterpolatedPositions = interpolatedPositions;
		mTrace = annotatdSsa.getTrace();
		mInstantiateArrayExt = instantiateArrayExt;
		final HashMap<Term, Term> const2RepTv = new HashMap<>();
		for (final Entry<Term, IProgramVar> entry : constants2BoogieVar.entrySet()) {
			const2RepTv.put(entry.getKey(), entry.getValue().getTermVariable());
		}
		if (mMgdScriptTc != mgdScriptCfg) {
			mConst2RepTvSubst =
					new TermTransferrer(mMgdScriptTc.getScript(), mMgdScriptCfg.getScript(), const2RepTv, true);
		} else {
			mConst2RepTvSubst = new SubstitutionWithLocalSimplification(mMgdScriptCfg, const2RepTv);
		}

		computeCraigInterpolants();
		traceCheck.cleanupAndUnlockSolver();
		for (int i = 0; i < mCraigInterpolants.length; i++) {
			mLogger.debug(new DebugMessage("NestedInterpolant {0}: {1}", i, mCraigInterpolants[i]));
		}
		mInterpolants = computePredicates();
		assert mInterpolants != null;
		// if (mPref.dumpFormulas()) {
		// dumpNestedStateFormulas(mInterpolants, mTrace, mIterationPW);
	}

	public void computeCraigInterpolants() {
		mInterpolInput = new ArrayList<>();
		mTreeStructure = new ArrayList<>();
		mCraigInt2interpolantIndex = new ArrayList<>();
		mStartOfCurrentSubtree = 0;
		mStartOfSubtreeStack = new Stack<>();
		mStackHeightAtLastInterpolatedPosition = 0;
		boolean startNewFormula = true;

		for (int i = 0; i < mAnnotSSA.getTrace().length(); i++) {
			// if last position was interpolated position we add new formula to
			// interpol input
			if (startNewFormula) {
				if (mTrace.isInternalPosition(i)) {
					newInterpolInputFormula(i);
				} else if (mTrace.isCallPosition(i)) {
					if (!mTrace.isPendingCall(i)) {
						final int nextPosition = mInterpolInput.size();
						mStartOfSubtreeStack.push(mStartOfCurrentSubtree);
						mStartOfCurrentSubtree = nextPosition;
					}
					newInterpolInputFormula(i);
					if (mTrace.isPendingCall(i)) {
						addToLastInterpolInputFormula(mAnnotSSA.getLocalVarAssignment(i));
						addToLastInterpolInputFormula(mAnnotSSA.getOldVarAssignment(i));
					}
				} else if (mTrace.isReturnPosition(i)) {
					if (mTrace.isPendingReturn(i)) {
						newInterpolInputFormula(i);
						addToLastInterpolInputFormula(mAnnotSSA.getLocalVarAssignment(i));
						addToLastInterpolInputFormula(mAnnotSSA.getOldVarAssignment(i));
						addToLastInterpolInputFormula(mAnnotSSA.getPendingContext(i));
					} else {
						mStartOfCurrentSubtree = mStartOfSubtreeStack.pop();
						newInterpolInputFormula(i);
						final int correspondingCallPosition = mTrace.getCallPosition(i);
						addToLastInterpolInputFormula(mAnnotSSA.getLocalVarAssignment(correspondingCallPosition));
						addToLastInterpolInputFormula(mAnnotSSA.getOldVarAssignment(correspondingCallPosition));
					}

				} else {
					throw new AssertionError();
				}

			} else {
				if (mTrace.isInternalPosition(i)) {
					addToLastInterpolInputFormula(mAnnotSSA.getFormulaFromNonCallPos(i));
				} else if (mTrace.isCallPosition(i)) {
					if (!mTrace.isPendingCall(i)) {
						mStartOfSubtreeStack.push(mStartOfCurrentSubtree);
						mStartOfCurrentSubtree = -23;
					}
					addToLastInterpolInputFormula(mAnnotSSA.getGlobalVarAssignment(i));
					if (mTrace.isPendingCall(i)) {
						addToLastInterpolInputFormula(mAnnotSSA.getLocalVarAssignment(i));
						addToLastInterpolInputFormula(mAnnotSSA.getOldVarAssignment(i));
					}
				} else if (mTrace.isReturnPosition(i)) {
					if (mTrace.isPendingReturn(i)) {
						addToLastInterpolInputFormula(mAnnotSSA.getFormulaFromNonCallPos(i));
						addToLastInterpolInputFormula(mAnnotSSA.getLocalVarAssignment(i));
						addToLastInterpolInputFormula(mAnnotSSA.getOldVarAssignment(i));
						addToLastInterpolInputFormula(mAnnotSSA.getPendingContext(i));
					} else {
						mStartOfCurrentSubtree = mStartOfSubtreeStack.pop();
						addToLastInterpolInputFormula(mAnnotSSA.getFormulaFromNonCallPos(i));
						final int correspondingCallPosition = mTrace.getCallPosition(i);
						addToLastInterpolInputFormula(mAnnotSSA.getLocalVarAssignment(correspondingCallPosition));
						addToLastInterpolInputFormula(mAnnotSSA.getOldVarAssignment(correspondingCallPosition));
					}
				} else {
					throw new AssertionError();
				}
			}
			startNewFormula = isInterpolatedPosition(i);
			if (isInterpolatedPosition(i)) {
				mStackHeightAtLastInterpolatedPosition = mStartOfSubtreeStack.size();
				mCraigInt2interpolantIndex.add(i);
			}

		}
		final Term[] interpolInput = mInterpolInput.toArray(new Term[0]);
		// add precondition to first term
		// special case: if first position is non pending call, then we add the
		// precondition to the corresponding return.
		if (mTrace.isCallPosition(0) && !mTrace.isPendingCall(0)) {
			final int correspondingReturn = mTrace.getReturnPosition(0);
			// if we do not interpolate at each position
			// interpolInput[correspondingReturn] might be the wrong position
			int interpolInputPositionOfReturn = 0;
			for (int i = 0; i < correspondingReturn; i++) {
				if (mInterpolatedPositions.contains(i)) {
					interpolInputPositionOfReturn++;
				}
			}
			interpolInput[interpolInputPositionOfReturn] = SmtUtils.and(mMgdScriptTc.getScript(),
					interpolInput[interpolInputPositionOfReturn], mAnnotSSA.getPrecondition());
		} else {
			interpolInput[0] = SmtUtils.and(mMgdScriptTc.getScript(), interpolInput[0], mAnnotSSA.getPrecondition());
		}
		// add negated postcondition to last term
		interpolInput[interpolInput.length - 1] = SmtUtils.and(mMgdScriptTc.getScript(),
				interpolInput[interpolInput.length - 1], mAnnotSSA.getPostcondition());

		final int[] startOfSubtree = integerListToIntArray(mTreeStructure);
		if (mTreeInterpolation) {
			mCraigInterpolants = mMgdScriptTc.getInterpolants(mScriptLockOwner, interpolInput, startOfSubtree);
		} else {
			mCraigInterpolants = mMgdScriptTc.getInterpolants(mScriptLockOwner, interpolInput);
		}

	}

	public static int[] integerListToIntArray(final List<Integer> integerList) {
		final int[] result = new int[integerList.size()];
		for (int i = 0; i < integerList.size(); i++) {
			result[i] = integerList.get(i);
		}
		return result;
	}

	private void newInterpolInputFormula(final int i) {
		if (mStackHeightAtLastInterpolatedPosition == mStartOfSubtreeStack.size()) {
			// everything ok
		} else {
			if (mStackHeightAtLastInterpolatedPosition + 1 == mStartOfSubtreeStack.size() && mTrace.isCallPosition(i)
					&& (i == 0 || isInterpolatedPosition(i - 1))) {
				// everything ok
			} else {
				if (mStackHeightAtLastInterpolatedPosition - 1 == mStartOfSubtreeStack.size()
						&& mTrace.isReturnPosition(i) && isInterpolatedPosition(i - 1)) {
					// everything ok
				} else {
					throw new IllegalArgumentException(
							"if you want to interpolate between call and return you have to interpolate after call and after return.");
				}
			}
		}
		Term term;
		if (mTrace.isCallPosition(i)) {
			term = mAnnotSSA.getGlobalVarAssignment(i);
		} else {
			term = mAnnotSSA.getFormulaFromNonCallPos(i);
		}
		mInterpolInput.add(term);
		// the interpolant between last formula and this new formula can be
		// found
		// at position i-1

		mTreeStructure.add(mStartOfCurrentSubtree);
	}

	private void addToLastInterpolInputFormula(final Term term) {
		final int lastPosition = mInterpolInput.size() - 1;
		final Term newFormula = SmtUtils.and(mMgdScriptTc.getScript(), mInterpolInput.get(lastPosition), term);
		assert newFormula != null : "newFormula must be != null";
		mInterpolInput.set(lastPosition, newFormula);
	}

	public boolean isInterpolatedPosition(final int i) {
		assert i >= 0;
		assert i < mTrace.length();
		if (i == mTrace.length() - 1) {
			return false;
		}
		if (mInterpolatedPositions == null) {
			return true;
		}
		return mInterpolatedPositions.contains(i);
	}

	public IPredicate[] getNestedInterpolants() {
		for (int j = 0; j < mInterpolants.length; j++) {
			mLogger.debug(new DebugMessage("Interpolant {0}: {1}", j, mInterpolants[j]));
		}
		return mInterpolants;
	}

	// /**
	// * Compute nested interpolants for given SSA. The result are the Craig
	// * interpolants for the SSA given as formula, the interpolants contain the
	// * variables with indices as they occur in the SSA. The result is written
	// * to mCraigInterpolants.
	// */
	// private void computeCraigInterpolants() {
	// // mCraigInterpolants[0] = mCsToolkit.getScript().term("true");
	// // mCraigInterpolants[mCraigInterpolants.length-1] =
	// mCsToolkit.getScript().term("false");
	// List<Integer> interpolProbStartPositions =
	// getInterpolProbStartPositions();
	// for (Integer k: interpolProbStartPositions) {
	// computeInterpolantSubsequence(k);
	// }
	// }
	//
	//
	//
	// /**
	// * Given a run, return all positions from where we have to start an
	// * interpolation problem. These positions are:
	// * <ul>
	// * <li> Position 0
	// * <li> Each call position where the call is not a pending call.
	// * </ul>
	// */
	// private List<Integer> getInterpolProbStartPositions() {
	// List<Integer> interpolProbStartPos = new LinkedList<Integer>();
	// // if (mPref.interprocedural()) {
	// for (int i=0; i<mTrace.length(); i++) {
	// if (mTrace.isCallPosition(i) && !mTrace.isPendingCall(i)) {
	// interpolProbStartPos.add(i);
	// }
	// }
	// if (interpolProbStartPos.isEmpty() ||
	// interpolProbStartPos.get(0) !=0 ) {
	// interpolProbStartPos.add(0, 0);
	// }
	// // }
	// // else {
	// // interpolProbStartPos.add(0);
	// // }
	// return interpolProbStartPos;
	// }

	// /**
	// * Given the SSA compute interpolants for a subsequence starting from
	// * position k and write the result to mCraigInterpolants.
	// * If k is a non-pending call position the end of the sequence is the
	// * corresponding return position. Otherwise k = 0 and the end position is
	// * the last position of the SSA.
	// * The interpolation subsequence consists of the corresponding SSA
	// * subsequence. If k!=0, we add two additional conjuncts. First the
	// * k-th interpolant (which has been computed yet). Second, the negation of
	// * the 'sequence end position'-th interpolant.
	// * @param k a non-pending call position of the mrun or 0
	// * @return true iff the interpolation subsequence is satisfiable
	// * @throws ölö
	// */
	// private boolean computeInterpolantSubsequence(int k) {
	// int endPos;
	// if (k==0) {
	// endPos = mAnnotSSA.getTerms().length-1;
	// }
	// else {
	// assert (mTrace.isCallPosition(k) &&
	// !mTrace.isPendingCall(k));
	// endPos = mTrace.getReturnPosition(k);
	// }
	// ArrayList<Term> interpolProb = new ArrayList<Term>();
	// ArrayList<Integer> indexTranslation = new ArrayList<Integer>();
	// Term interproceduralLinkPendingCalls =
	// mCsToolkit.getScript().term("true");
	// int j=0;
	// interpolProb.add(j, getFormulaforPos(k));
	// for (int i=k+1; i<= endPos; i++) {
	// Term iFormu = getFormulaforPos(i);
	// if (mTrace.isPendingCall(i)) {
	// interproceduralLinkPendingCalls = SmtUtils.and(mScript,
	// interproceduralLinkPendingCalls,
	// mAnnotSSA.getTerms()[i]);
	// }
	// if (isInterpolatedPosition(i)) {
	// j++;
	// indexTranslation.add(i);
	// interpolProb.add(j,iFormu);
	// }
	// else {
	// Term jFormu = interpolProb.get(j);
	// interpolProb.set(j,SmtUtils.and(mScript,jFormu,iFormu));
	// }
	// }
	// Term lastTerm = interpolProb.get(j);
	//
	// if (k !=0 ) {
	// for (int i = 0; i<k; i++) {
	// if (mTrace.isPendingCall(i)) {
	// interproceduralLinkPendingCalls = SmtUtils.and(mScript,
	// interproceduralLinkPendingCalls,
	// mAnnotSSA.getTerms()[i]);
	// }
	// lastTerm = SmtUtils.and(mScript,lastTerm, getFormulaforPos(i));
	// }
	// for (int i=endPos+1; i<mAnnotSSA.length(); i++) {
	// if (mTrace.isPendingCall(i)) {
	// interproceduralLinkPendingCalls = SmtUtils.and(mScript,
	// interproceduralLinkPendingCalls,
	// mAnnotSSA.getTerms()[i]);
	// }
	// lastTerm = SmtUtils.and(mScript,lastTerm, getFormulaforPos(i));
	// }
	// }
	// else {
	// lastTerm = SmtUtils.and(mScript,lastTerm, interproceduralLinkPendingCalls);
	// }
	// interpolProb.set(j,lastTerm);
	// assert (interpolProb.size()-1 == indexTranslation.size());
	//
	// Term[] interpolInput = interpolProb.toArray(new Term[0]);
	//
	// if (mIterationPW != null) {
	// String line;
	// line = "=====InterpolationProblem starting from position " + k;
	// s_Logger.debug(line);
	// mIterationPW.println(line);
	// // dumpInterpolationInput(k, interpolInput, indexTranslation,
	// (NestedRun<CodeBlock, Predicate>) mRun, mScript, mIterationPW);
	// // SmtManager.dumpInterpolProblem(interpolInput, mIteration, k,
	// mPref.dumpPath(), mScript);
	// }
	// Term[] interpolOutput = null;
	// if (interpolInput.length > 1) {
	// interpolOutput = mCsToolkit.computeInterpolants(interpolInput);
	// }
	//
	//
	// if (mIterationPW != null) {
	// // dumpInterpolationOutput(k, interpolOutput,
	// indexTranslation,mRun.getWord(), mIterationPW);
	// }
	//
	// for (int jj = 0; jj<indexTranslation.size(); jj++) {
	// mCraigInterpolants[indexTranslation.get(jj)-1] = interpolOutput[jj];
	// }
	// return false;
	// }

	// private Term getFormulaforPos(int i) {
	// Term iFormu;
	// if (mTrace.isInternalPosition(i)) {
	// iFormu = mAnnotSSA.getTerms()[i];
	// } else if (mTrace.isCallPosition(i)) {
	// iFormu = mCsToolkit.getScript().term("true");
	// } else if (mTrace.isReturnPosition(i)) {
	// iFormu = mAnnotSSA.getTerms()[i];
	// int callPos = mTrace.getCallPosition(i);
	// SmtUtils.and(mScript, iFormu, mAnnotSSA.getTerms()[callPos]);
	// } else {
	// throw new AssertionError();
	// }
	// return iFormu;
	// }

	// //FIXME wrong - fixed?
	// private boolean isInterpolatedPosition(int i) {
	// if (mInterpolatedPositions == null) {
	// return true;
	// }
	// //interpolate for cutpoint positions
	// // if (mcutpoints.contains(((NestedRun<CodeBlock, Predicate>)
	// mRun).getStateAtPosition(i).getProgramPoint())) {
	// // return true;
	// // }
	// //interpolate before calls
	// if (mTrace.isCallPosition(i)) {
	// return true;
	// }
	// //interpolate after returns
	// if (i>0 && mTrace.isReturnPosition(i-1)) {
	// return true;
	// }
	// return false;
	// }

	private IPredicate[] computePredicates() {
		final IPredicate[] result = new IPredicate[mTrace.length() - 1];
		assert mCraigInterpolants.length == mCraigInt2interpolantIndex.size();
		// assert mInterpolatedPositions.size() == mCraigInterpolants.length;

		final Map<Term, IPredicate> withIndices2Predicate = new HashMap<>();

		int craigInterpolPos = 0;
		for (int resultPos = 0; resultPos < mTrace.length() - 1; resultPos++) {
			checkTimeout();
			int positionOfThisCraigInterpolant;
			if (craigInterpolPos == mCraigInterpolants.length) {
				// special case where trace ends with return
				// we already added all CraigInterpolants
				// remaining interpolants are "unknown" and the implicit given
				// false at the end
				assert mTrace.isReturnPosition(mTrace.length() - 1);
				positionOfThisCraigInterpolant = Integer.MAX_VALUE;
			} else {
				positionOfThisCraigInterpolant = mCraigInt2interpolantIndex.get(craigInterpolPos);
			}
			assert positionOfThisCraigInterpolant >= resultPos;
			if (isInterpolatedPosition(resultPos)) {
				Term withIndices = mCraigInterpolants[craigInterpolPos];
				assert resultPos == mCraigInt2interpolantIndex.get(craigInterpolPos);
				craigInterpolPos++;
				result[resultPos] = withIndices2Predicate.get(withIndices);
				if (result[resultPos] == null) {
					/*
					 * remove all let terms added because iZ3's interpolants contain let terms better solution:
					 * implement support for let terms in SafeSubstitution
					 */
					withIndices = new FormulaUnLet().transform(withIndices);
					Term withoutIndices = mConst2RepTvSubst.transform(withIndices);
					if (mInstantiateArrayExt) {
						withoutIndices = instantiateArrayExt(withoutIndices);
					}
					if (!ALLOW_AT_DIFF
							&& new SubtermPropertyChecker(x -> isAtDiffTerm(x)).isPropertySatisfied(withoutIndices)) {
						throw new UnsupportedOperationException(DIFF_IS_UNSUPPORTED);
					}
					final Term withoutIndicesNormalized = new ConstantTermNormalizer().transform(withoutIndices);
					Term lessQuantifiers;
					try {
						lessQuantifiers = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScriptCfg,
								withoutIndicesNormalized, mSimplificationTechnique, mXnfConversionTechnique);
					} catch (final AssertionError ae) {
						if (IGNORE_PQE_ERROR) {
							lessQuantifiers = withoutIndicesNormalized;
						} else {
							throw ae;
						}
					}
					result[resultPos] = mPredicateUnifier.getOrConstructPredicate(lessQuantifiers);
					withIndices2Predicate.put(withIndices, result[resultPos]);
				}
			} else {
				result[resultPos] = mPredicateFactory.newDontCarePredicate(null);
			}
		}
		assert craigInterpolPos == mCraigInterpolants.length;
		return result;
	}

	private void checkTimeout() {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new ToolchainCanceledException(this.getClass(),
					"constructing predicates for " + (mTrace.length() - 1) + " interpolants");
		}
	}

	/**
	 * The interpolating Z3 generates Craig interpolants that contain the array-ext function whose semantics is defined
	 * by the following axiom ∀a∀b∃k. array-ext(a,b)=k <--> (a=b \/ a[k] != b[k]). The theory of arrays does not contain
	 * this axiom, hence we instantiate it for each occurrence.
	 */
	private Term instantiateArrayExt(final Term interpolantWithoutIndices) {
		final Term nnf = new NnfTransformer(mMgdScriptCfg, mServices, QuantifierHandling.PULL)
				.transform(interpolantWithoutIndices);
		// not needed, at the moment our NNF transformation also produces
		// Term prenex = (new PrenexNormalForm(mCsToolkitPredicates.getScript(),
		// mCsToolkitPredicates.getVariableManager())).transform(nnf);
		final QuantifierSequence qs = new QuantifierSequence(mMgdScriptCfg.getScript(), nnf);
		// The quantifier-free part of of formula in prenex normal form is called
		// matrix
		final Term matrix = qs.getInnerTerm();

		final ApplicationTermFinder atf = new ApplicationTermFinder("array-ext", false);
		final Set<ApplicationTerm> arrayExtAppTerms = atf.findMatchingSubterms(matrix);
		if (arrayExtAppTerms.isEmpty()) {
			return interpolantWithoutIndices;
		}
		final Term[] implications = new Term[arrayExtAppTerms.size()];
		final TermVariable[] replacingTermVariable = new TermVariable[arrayExtAppTerms.size()];
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		int offset = 0;
		for (final ApplicationTerm appTerm : arrayExtAppTerms) {
			final ArrayExtTerm aet = new ArrayExtTerm(appTerm);
			replacingTermVariable[offset] = aet.getReplacementTermVariable();
			implications[offset] = aet.getImplication();
			substitutionMapping.put(aet.getArrayExtTerm(), aet.getReplacementTermVariable());
			offset++;
		}
		Term result = new Substitution(mMgdScriptCfg.getScript(), substitutionMapping).transform(matrix);
		result = SmtUtils.and(mMgdScriptCfg.getScript(), result, SmtUtils.and(mMgdScriptCfg.getScript(), implications));
		result = mMgdScriptCfg.getScript().quantifier(QuantifiedFormula.EXISTS, replacingTermVariable, result);
		result = QuantifierSequence.prependQuantifierSequence(mMgdScriptCfg.getScript(), qs.getQuantifierBlocks(),
				result);
		// Term pushed = new QuantifierPusher(mCsToolkitPredicates.getScript(), mServices).transform(result);
		return result;
	}

	private class ArrayExtTerm {
		private final ApplicationTerm mArrayExtTerm;
		private final Term mFirstArray;
		private final Term mSecondArray;
		private final TermVariable mReplacementTermVariable;
		private final Term mImplication;

		public ArrayExtTerm(final ApplicationTerm arrayExtTerm) {
			mArrayExtTerm = arrayExtTerm;
			if (!mArrayExtTerm.getFunction().getName().equals("array-ext")) {
				throw new IllegalArgumentException("no array-ext Term");
			}
			if (mArrayExtTerm.getParameters().length != 2) {
				throw new IllegalArgumentException("expected two params");
			}
			mFirstArray = mArrayExtTerm.getParameters()[0];
			mSecondArray = mArrayExtTerm.getParameters()[1];
			mReplacementTermVariable =
					arrayExtTerm.getTheory().createFreshTermVariable("arrExt", arrayExtTerm.getSort());
			mImplication = constructImplication();
		}

		private Term constructImplication() {
			final Term arraysDistinct = mMgdScriptCfg.getScript().term("distinct", mFirstArray, mSecondArray);
			final Term firstSelect = SmtUtils.select(mMgdScriptCfg.getScript(), mFirstArray, mReplacementTermVariable);
			final Term secondSelect =
					SmtUtils.select(mMgdScriptCfg.getScript(), mSecondArray, mReplacementTermVariable);
			final Term selectDistinct = mMgdScriptCfg.getScript().term("distinct", firstSelect, secondSelect);
			final Term implication = Util.implies(mMgdScriptCfg.getScript(), arraysDistinct, selectDistinct);
			return implication;
		}

		public ApplicationTerm getArrayExtTerm() {
			return mArrayExtTerm;
		}

		public Term getFirstArray() {
			return mFirstArray;
		}

		public Term getSecondArray() {
			return mSecondArray;
		}

		public TermVariable getReplacementTermVariable() {
			return mReplacementTermVariable;
		}

		public Term getImplication() {
			return mImplication;
		}

	}

	private static void dumpInterpolationInput(final int offset, final Term[] interpolInput,
			final List<Integer> indexTranslation, final NestedRun<CodeBlock, IPredicate> run, final Script theory,
			final PrintWriter pW, final ILogger logger) {
		String line;
		int indentation = 0;
		int translatedPosition;
		final FormulaUnLet unflet = new FormulaUnLet();
		try {
			line = "==Interpolation Input";
			logger.debug(line);
			pW.println(line);
			for (int j = 0; j < interpolInput.length; j++) {
				if (j == 0) {
					translatedPosition = offset;
				} else {
					translatedPosition = indexTranslation.get(j - 1);
				}
				line = AbstractCegarLoop.addIndentation(indentation, "Location " + translatedPosition + ": "
						+ ((SPredicate) run.getStateAtPosition(translatedPosition)).getProgramPoint());
				logger.debug(line);
				pW.println(line);
				if (run.isCallPosition(translatedPosition)) {
					indentation++;
				}
				line = AbstractCegarLoop.addIndentation(indentation, unflet.unlet(interpolInput[j]).toString());
				logger.debug(line);
				pW.println(line);
				if (run.isReturnPosition(translatedPosition)) {
					indentation--;
				}
			}
			if (offset != 0) {
				final int returnSuccPos = run.getWord().getReturnPosition(offset) + 1;
				line = AbstractCegarLoop.addIndentation(indentation, "Location " + returnSuccPos + ": "
						+ ((SPredicate) run.getStateAtPosition(returnSuccPos)).getProgramPoint());
				logger.debug(line);
				pW.println(line);
			}
			pW.println("");
			pW.println("");
		} finally {
			pW.flush();
		}
	}

	private static void dumpInterpolationOutput(final int offset, final Term[] interpolOutput,
			final List<Integer> indexTranslation, final Word<CodeBlock> run, final PrintWriter pW,
			final ILogger logger) {
		final NestedWord<CodeBlock> word = NestedWord.nestedWord(run);
		assert interpolOutput.length == indexTranslation.size();
		String line;
		int indentation = 0;
		int translatedPosition;
		try {
			line = "==Interpolation Output";
			logger.debug(line);
			pW.println(line);
			for (int j = 0; j < interpolOutput.length; j++) {
				translatedPosition = indexTranslation.get(j);
				if (translatedPosition > 1 && word.isCallPosition(translatedPosition - 1)) {
					indentation++;
				}
				line = AbstractCegarLoop.addIndentation(indentation,
						"InterpolOutput" + translatedPosition + ": " + interpolOutput[j]);
				logger.debug(line);
				pW.println(line);
				if (word.isReturnPosition(translatedPosition)) {
					indentation--;
				}
			}
			pW.println("");
			pW.println("");
		} finally {
			pW.flush();
		}
	}

	private static void dumpNestedStateFormulas(final IPredicate[] stateFormulas, final Word<CodeBlock> word,
			final PrintWriter pW, final ILogger logger) {
		final NestedWord<CodeBlock> nw = NestedWord.nestedWord(word);
		assert stateFormulas.length == word.length() + 1;
		String line;
		int indentation = 0;
		try {
			line = "==NestedInterpolants";
			logger.debug(line);
			pW.println(line);
			for (int j = 0; j < stateFormulas.length; j++) {
				line = AbstractCegarLoop.addIndentation(indentation, j + ": " + stateFormulas[j]);
				logger.debug(line);
				pW.println(line);
				if (j != stateFormulas.length - 1) {
					pW.println(word.getSymbol(j));
					if (nw.isCallPosition(j)) {
						indentation++;
					}
					if (nw.isReturnPosition(j)) {
						indentation--;
					}
				}
			}
		} finally {
			pW.flush();
		}
	}

	private static boolean isAtDiffTerm(final Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName().equals("@diff");
		}
		return false;
	}

}
