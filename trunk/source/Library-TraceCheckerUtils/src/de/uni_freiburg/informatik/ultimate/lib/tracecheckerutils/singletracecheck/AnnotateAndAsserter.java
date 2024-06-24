/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.VarAssignmentReuseAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer.TestGenReuseMode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * TODO: use quick check
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de), Max Barth (Max.Barth@lmu.de)
 */
public class AnnotateAndAsserter<L extends IAction> {

	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;

	protected final ManagedScript mMgdScriptTc;
	protected final NestedWord<L> mTrace;

	protected LBool mSatisfiable;
	protected final NestedFormulas<L, Term, Term> mSSA;
	protected ModifiableNestedFormulas<L, Term, Term> mAnnotSSA;

	protected final AnnotateAndAssertCodeBlocks<L> mAnnotateAndAssertCodeBlocks;

	protected final TraceCheckStatisticsGenerator mTcbg;

	public boolean mSucessfulReuse = false;
	private VarAssignmentReuseAnnotation mVAforReuse = null;
	private VarAssignmentReuseAnnotation mCurrentVA;
	private VarAssignmentReuseAnnotation mDefaultVA;
	final LinkedHashSet<String> nondetsInTrace = new LinkedHashSet<String>();
	final LinkedHashSet<String> nondetsInTraceAfterPreviousVA = new LinkedHashSet<String>();
	final HashMap<String, String> nondetNameToType = new HashMap<>();
	public ArrayList<VarAssignmentReuseAnnotation> mVAsInPrefix = new ArrayList<VarAssignmentReuseAnnotation>();
	final HashMap<String, String> procedureToCallLoc = new HashMap<>();
	private int mReuseCandidatePosition = 0;
	private final Integer mHighestVaOrderInTrace = -1;
	private boolean reuseUnsatpossible;
	private final ArrayList<Pair<Term, Term>> mValueAssignmentUsedForReuse = new ArrayList<Pair<Term, Term>>();

	final TestGenReuseMode mTestGenReuseMode;

	public AnnotateAndAsserter(final ManagedScript mgdScriptTc, final NestedFormulas<L, Term, Term> nestedSSA,
			final AnnotateAndAssertCodeBlocks<L> aaacb, final TraceCheckStatisticsGenerator tcbg,
			final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(TraceCheckerUtils.PLUGIN_ID);
		mMgdScriptTc = mgdScriptTc;
		mTrace = nestedSSA.getTrace();
		mSSA = nestedSSA;
		mAnnotateAndAssertCodeBlocks = aaacb;
		mTcbg = tcbg;
		mTestGenReuseMode = RcfgPreferenceInitializer.getPreferences(services)
				.getEnum(RcfgPreferenceInitializer.LABEL_TEST_GEN_REUSE_MODE, TestGenReuseMode.class);
		reuseUnsatpossible = mTestGenReuseMode.equals(TestGenReuseMode.ReuseUNSATmatchPrefix)
				|| mTestGenReuseMode.equals(TestGenReuseMode.ReuseUNSATmatchCalloc);
	}

	public void buildAnnotatedSsaAndAssertTerms() {
		boolean reuse = true;
		if (mTestGenReuseMode.equals(TestGenReuseMode.ReuseUNSATmatchPrefix)) {
			getReuseCandidate();
			if (mVAforReuse == null) {
				reuse = false;
			}
		}
		if (mAnnotSSA != null) {
			throw new AssertionError("already build");
		}
		assert mSatisfiable == null;

		mAnnotSSA = new ModifiableNestedFormulas<>(mTrace, new TreeMap<Integer, Term>());

		mAnnotSSA.setPrecondition(mAnnotateAndAssertCodeBlocks.annotateAndAssertPrecondition());
		mAnnotSSA.setPostcondition(mAnnotateAndAssertCodeBlocks.annotateAndAssertPostcondition());

		final Collection<Integer> callPositions = new ArrayList<>();
		final Collection<Integer> pendingReturnPositions = new ArrayList<>();
		int branchCount = 0;
		for (int i = 0; i < mTrace.length(); i++) {
			if (mTrace.isCallPosition(i)) {
				callPositions.add(i);
				mAnnotSSA.setGlobalVarAssignmentAtPos(i,
						mAnnotateAndAssertCodeBlocks.annotateAndAssertGlobalVarAssignemntCall(i));
				mAnnotSSA.setLocalVarAssignmentAtPos(i,
						mAnnotateAndAssertCodeBlocks.annotateAndAssertLocalVarAssignemntCall(i));
				mAnnotSSA.setOldVarAssignmentAtPos(i,
						mAnnotateAndAssertCodeBlocks.annotateAndAssertOldVarAssignemntCall(i));

			} else {
				if (mTrace.isReturnPosition(i) && mTrace.isPendingReturn(i)) {
					pendingReturnPositions.add(i);
				}
				mAnnotSSA.setFormulaAtNonCallPos(i, mAnnotateAndAssertCodeBlocks.annotateAndAssertNonCall(i));
			}

			// ensure we are not considering currentVA as reuseCandidate
			if (i < mTrace.length() - 1 && !mTestGenReuseMode.equals(TestGenReuseMode.None)) {

				// calling loc version
				if (mTestGenReuseMode.equals(TestGenReuseMode.ReuseUNSATmatchCalloc)) {
					if (mTrace.getSymbol(i) instanceof Call) {
						final Call call = (Call) mTrace.getSymbol(i);
						if (procedureToCallLoc.containsKey(call.getSucceedingProcedure())) {
							procedureToCallLoc.remove(call.getSucceedingProcedure());
						}
						procedureToCallLoc.put(call.getSucceedingProcedure(), call.getSource().toString());
					}
				}

				if (mSSA.getTrace().getSymbol(i) instanceof StatementSequence) {
					final StatementSequence statementBranch = (StatementSequence) mSSA.getTrace().getSymbol(i);
					ifStatementHasNondetAddToSet(i, statementBranch);
					if (statementBranch.getPayload().getAnnotations()
							.containsKey(VarAssignmentReuseAnnotation.class.getName())) {
						final VarAssignmentReuseAnnotation vaInTrace = (VarAssignmentReuseAnnotation) statementBranch
								.getPayload().getAnnotations().get(VarAssignmentReuseAnnotation.class.getName());
						// prefix
						if (mTestGenReuseMode.equals(TestGenReuseMode.ReuseUNSATmatchPrefix) && reuse) {
							mVAsInPrefix.add(vaInTrace);
							assert i <= mReuseCandidatePosition;
							if (i < mReuseCandidatePosition) {
								if (branchCount < mVAforReuse.mVAsInVAPrefix.size()) { //
									if (!mVAforReuse.mVAsInVAPrefix.get(branchCount).equals(vaInTrace)) {
										reuse = false;
									}
								} else {
									reuse = false;
								}
							} else if (i == mReuseCandidatePosition) {
								nondetsInTraceAfterPreviousVA.clear();
							}
							branchCount += 1;

							// Ensure we do not consider currentVA for reuse
						} else {
							// default reuse
							mVAforReuse = vaInTrace;
							nondetsInTraceAfterPreviousVA.clear();
							if (mTestGenReuseMode.equals(TestGenReuseMode.ReuseUNSATmatchCalloc)) {
								final String precedingProc = statementBranch.getPrecedingProcedure();
								// Check if annotated test-goal and current test-goal are in the same procedure
								// And have the same calling location (incoming icfg edge)
								if (!mVAforReuse.getPrecedingProcedure().equals(precedingProc)
										&& mVAforReuse.mLocationOfPrecedingProcedure
												.equals(procedureToCallLoc.get(precedingProc))) {
									reuseUnsatpossible = false;
								}
							}

						}
					}
				}
			}
		}

		assert callPositions.containsAll(mTrace.getCallPositions());
		assert mTrace.getCallPositions().containsAll(callPositions);

		// number that the pending context. The first pending context has
		// number -1, the second -2, ...
		int pendingContextCode = -1 - mSSA.getTrace().getPendingReturns().size();

		for (final Integer positionOfPendingReturn : mSSA.getTrace().getPendingReturns().keySet()) {
			assert mTrace.isPendingReturn(positionOfPendingReturn);
			{
				final Term annotated = mAnnotateAndAssertCodeBlocks
						.annotateAndAssertPendingContext(positionOfPendingReturn, pendingContextCode);
				mAnnotSSA.setPendingContext(positionOfPendingReturn, annotated);
			}
			{
				final Term annotated = mAnnotateAndAssertCodeBlocks
						.annotateAndAssertLocalVarAssignemntPendingContext(positionOfPendingReturn, pendingContextCode);
				mAnnotSSA.setLocalVarAssignmentAtPos(positionOfPendingReturn, annotated);
			}
			{
				final Term annotated = mAnnotateAndAssertCodeBlocks
						.annotateAndAssertOldVarAssignemntPendingContext(positionOfPendingReturn, pendingContextCode);
				mAnnotSSA.setOldVarAssignmentAtPos(positionOfPendingReturn, annotated);
			}
			pendingContextCode++;
		}

		if (!mTestGenReuseMode.equals(TestGenReuseMode.None)) {
			getCurrentVA();
			if (mCurrentVA != null && mVAforReuse == null && reuseUnsatpossible) {
				mDefaultVA = mCurrentVA.setDefaultVa(mDefaultVA);
				mDefaultVA = mCurrentVA.mVAofOppositeBranch.setDefaultVa(mDefaultVA);
				mVAforReuse = mDefaultVA;
			}

			if (nondetsInTrace.isEmpty() || mCurrentVA == null || mVAforReuse == null) {
				reuse = false;
			} else if (mVAforReuse.mNegatedVA) {
				reuse = false;
			} else if (mCurrentVA.mUnsatWithVAs.contains(mVAforReuse) && mVAforReuse.mNegatedVA == false) {
				reuse = false; // Wie kann das überhaupt sein?
				// System.out.println("NO REUSE since UNSAT With");
			} else if (mVAforReuse.mVarAssignmentPair.isEmpty()) {
				reuse = false;
			} else if (reuse) {
				ArrayList<Term> vaPairsAsTerms;
				if (mTestGenReuseMode.equals(TestGenReuseMode.Reuse) || !reuseUnsatpossible) {
					vaPairsAsTerms = getNonDetsAsTermsReuse();
				} else if (reuseUnsatpossible) {
					vaPairsAsTerms = getNonDetsAsTermsReuseUNSAT();
				} else {
					throw new AssertionError("unexpected Reuse Mode");
				}

				if (!vaPairsAsTerms.isEmpty()) {
					final Term varAssignmentConjunction = SmtUtils.and(mMgdScriptTc.getScript(), vaPairsAsTerms);
					mMgdScriptTc.getScript().push(1);
					mAnnotateAndAssertCodeBlocks.annotateAndAssertTerm(varAssignmentConjunction, "Int");
					System.out.println("REUSE: " + varAssignmentConjunction);
				} else {
					reuse = false; // Can be empty if previous test goal is "behind" the current. (loops)
					// In this case previous test goal has not been checked yet.
				}

			} else {
				// System.out.println("no reuse because prefix doesnt match");
			}
			mSatisfiable = mMgdScriptTc.getScript().checkSat();

			if (reuse) {
				System.out.println("trying to reuse");
			}
			if (mSatisfiable == LBool.UNSAT) {
				if (reuse) {
					// System.out.println("REUSE UNSAT");
					mMgdScriptTc.getScript().pop(1);
					if (reuseUnsatpossible) {
						removeCheckIfCovered();
					}
					mSatisfiable = mMgdScriptTc.getScript().checkSat();
					if (mCurrentVA.secondCheck == true) {
						mVAforReuse.mNegatedVA = false;
					} else {
						mVAforReuse.mNegatedVA = true;
					}
				}
			} else if (reuse) {
				// register "other branch" as not reachable with this VA. Add negated VA to other branch test goal
				System.out.println("REUSE SUCCESSFULL");
				if (mCurrentVA.secondCheck == true) {
					mVAforReuse.mNegatedVA = !mVAforReuse.mNegatedVA;
				}
				mSucessfulReuse = true;
			}
			if (reuse) {
				mCurrentVA.secondCheck = true;
			}
		} else {
			mSatisfiable = mMgdScriptTc.getScript().checkSat();

		}
		if (mSatisfiable == LBool.SAT && mCurrentVA != null) {
			mCurrentVA.mCoveredTestGoal = true;

			// concreteExecution();

		}
		if (mSatisfiable == LBool.UNKNOWN) {
			// System.out.println("UNKNOWN");
		}

		// Report benchmarks
		mTcbg.reportNewCheckSat();
		mTcbg.reportNewCodeBlocks(mTrace.length());
		mTcbg.reportNewAssertedCodeBlocks(mTrace.length());
		mLogger.info("Conjunction of SSA is " + mSatisfiable);
	}

	/*
	 * In test case generation, we have a branching that is followed by a branching into assert true and assert !false.
	 * Where assert !false is an endpoint.
	 * The concrete value that reaches assert !false also satisfies assert true, where the program continues.
	 */
	private void concreteExecution() {
		final L word = mTrace.getSymbol(mTrace.length() - 3); // test goal branching. -3 should be the real branching
																// condition

		System.out.println("Branching word: " + word);
		if (word instanceof IcfgEdge) {
			((IcfgEdge) word).getTarget();
			System.out.println(((IcfgEdge) word).getTarget().getOutgoingEdges());
		}
		if (word instanceof CodeBlock) {
			((CodeBlock) word).getTarget();

			System.out.println(((CodeBlock) word).getTarget().getOutgoingEdges());
		}

		// word formula
		System.out.println(((IcfgEdge) word).getTransformula().getFormula());

		for (final IcfgEdge outgoing : ((IcfgEdge) word).getTarget().getOutgoingEdges()) {
			System.out.println("outgoing: " + outgoing);
			System.out.println(outgoing.getTransformula().getFormula());
			System.out.println(outgoing.getTarget());
			for (final IcfgEdge outgoing2 : outgoing.getTarget().getOutgoingEdges()) {
				System.out.println("outgoing2: " + outgoing2);
				System.out.println(outgoing2.getTransformula().getFormula());
				System.out.println(outgoing2.getTarget());
				for (final IcfgEdge outgoing3 : outgoing2.getTarget().getOutgoingEdges()) {
					System.out.println("outgoing3: " + outgoing3);
					System.out.println(outgoing3.getTransformula().getFormula());
					System.out.println(outgoing3.getTarget());
				}
			}
		}
		System.out.println("asd");
		/*
		 * letter bekommen wir vom automaten, vlt besser dass dann im tracecheck oder nwa zu machen sogar wobei nich so gut
		 */
		// final NestedWord<L> traceContinued = mTrace;
		// final NestedWord<L> subwordBefore = traceContinued.getSubWord(mTrace.length() - 2, mTrace.length() - 1);
		// final NestedWord<L> subwordBefore = traceContinued.7getSubWord(mTrace.length() - 2, mTrace.length() - 1);

		// traceContinued.concatenate(new NestedWord<>(((Object) word).getLetter(), -2));
		// traceContinued.concatenate(subwordBefore);
	}

	private Term createTermFromVA(final String variableAsString, final Term value) {
		FunctionSymbol varInCurrentScript =
				mMgdScriptTc.getScript().getTheory().getDeclaredFunctions().get(variableAsString);
		if (varInCurrentScript == null) {
			varInCurrentScript = mMgdScriptTc.getScript().getTheory()
					.getFunction(variableAsString.substring(1, variableAsString.length() - 1));
		}

		if (varInCurrentScript == null) {
			throw new AssertionError("unknown var " + variableAsString);
		}

		final Term nondetVar = SmtUtils.unfTerm(mMgdScriptTc.getScript(), varInCurrentScript);

		final Term nondetValue;

		switch (nondetVar.getSort().getName()) {
		case SmtSortUtils.FLOATINGPOINT_SORT: {

			if (nondetVar.getSort().getIndices()[1].equals("24")) {
				if (value != null) {
					final ApplicationTerm valueAsAppterm = (ApplicationTerm) value;
					nondetValue = SmtUtils.unfTerm(mMgdScriptTc.getScript(), valueAsAppterm.getFunction().getName(),
							valueAsAppterm.getSort().getIndices(), null, valueAsAppterm.getParameters());
				} else {
					// (fp (_ BitVec 1) (_ BitVec eb) (_ BitVec i) (_ FloatingPoint eb sb))
					// (_ +zero 2 4)

					final String[] indices = new String[2];
					indices[0] = "0";
					indices[1] = "0";

					final Term bvConst0 = SmtUtils.rational2Term(mMgdScriptTc.getScript(), Rational.ZERO,
							SmtSortUtils.getBitvectorSort(mMgdScriptTc.getScript(), 1));
					final Term bvConst1 = SmtUtils.rational2Term(mMgdScriptTc.getScript(), Rational.ZERO,
							SmtSortUtils.getBitvectorSort(mMgdScriptTc.getScript(), 8));
					final Term bvConst2 = SmtUtils.rational2Term(mMgdScriptTc.getScript(), Rational.ZERO,
							SmtSortUtils.getBitvectorSort(mMgdScriptTc.getScript(), 23));
					nondetValue =
							SmtUtils.unfTerm(mMgdScriptTc.getScript(), "fp", null, null, bvConst0, bvConst1, bvConst2);

					// nondetValue = SmtUtils.unfTerm(mMgdScriptTc.getScript(), "_ FloatingPoint 0 0", indices,
					// SmtSortUtils
					// .getFloatSort(mMgdScriptTc.getScript(), BigInteger.valueOf(8), BigInteger.valueOf(23)));

				}
			} else if (nondetVar.getSort().getIndices()[1].equals("53")) {

				if (value != null) {
					final ApplicationTerm valueAsAppterm = (ApplicationTerm) value;
					nondetValue = SmtUtils.unfTerm(mMgdScriptTc.getScript(), valueAsAppterm.getFunction().getName(),
							null, null, valueAsAppterm.getParameters());
				} else {
					// (fp (_ BitVec 1) (_ BitVec eb) (_ BitVec i) (_ FloatingPoint eb sb))
					// (_ +zero 2 4)

					final String[] indices = new String[2];
					indices[0] = "0";
					indices[1] = "0";

					final Term bvConst0 = SmtUtils.rational2Term(mMgdScriptTc.getScript(), Rational.ZERO,
							SmtSortUtils.getBitvectorSort(mMgdScriptTc.getScript(), 1));
					final Term bvConst1 = SmtUtils.rational2Term(mMgdScriptTc.getScript(), Rational.ZERO,
							SmtSortUtils.getBitvectorSort(mMgdScriptTc.getScript(), 11));
					final Term bvConst2 = SmtUtils.rational2Term(mMgdScriptTc.getScript(), Rational.ZERO,
							SmtSortUtils.getBitvectorSort(mMgdScriptTc.getScript(), 52));
					nondetValue =
							SmtUtils.unfTerm(mMgdScriptTc.getScript(), "fp", null, null, bvConst0, bvConst1, bvConst2);

					// nondetValue = SmtUtils.unfTerm(mMgdScriptTc.getScript(), "_ FloatingPoint 0 0", indices,
					// SmtSortUtils
					// .getFloatSort(mMgdScriptTc.getScript(), BigInteger.valueOf(8), BigInteger.valueOf(23)));

				}

			} else {
				throw new AssertionError("Unexpected Float Sort Size");
			}

			break;
		}
		case SmtSortUtils.BITVECTOR_SORT: {
			if (value != null) {
				final ApplicationTerm valueAsAppterm = (ApplicationTerm) value;
				final BigInteger constValue = new BigInteger(valueAsAppterm.getFunction().getName().substring(2));
				nondetValue = BitvectorUtils.constructTerm(mMgdScriptTc.getScript(),
						BitvectorUtils.constructBitvectorConstant(constValue, nondetVar.getSort()));
			} else {
				final BigInteger constValue = BigInteger.ZERO;
				nondetValue = BitvectorUtils.constructTerm(mMgdScriptTc.getScript(),
						BitvectorUtils.constructBitvectorConstant(constValue, nondetVar.getSort()));
			}
			break;
		}
		case SmtSortUtils.INT_SORT: {

			if (value != null) {
				nondetValue = SmtUtils.rational2Term(mMgdScriptTc.getScript(),
						SmtUtils.toRational(((ConstantTerm) value)), SmtSortUtils.getIntSort(mMgdScriptTc));
			} else {
				nondetValue = SmtUtils.constructIntegerValue(mMgdScriptTc.getScript(),
						SmtSortUtils.getIntSort(mMgdScriptTc), BigInteger.ZERO);
			}
			break;
		}
		case SmtSortUtils.REAL_SORT: {

			if (value != null) {
				nondetValue = SmtUtils.rational2Term(mMgdScriptTc.getScript(),
						SmtUtils.toRational(((ConstantTerm) value)), SmtSortUtils.getRealSort(mMgdScriptTc));
			} else {
				nondetValue = SmtUtils.constructIntegerValue(mMgdScriptTc.getScript(),
						SmtSortUtils.getRealSort(mMgdScriptTc), BigInteger.ZERO);
			}
			break;
		}
		default: {
			throw new AssertionError("Unexpected Value Sort");
		}
		}
		mValueAssignmentUsedForReuse.add(new Pair<>(nondetVar, nondetValue));
		return SmtUtils.binaryEquality(mMgdScriptTc.getScript(), nondetVar, nondetValue);
	}

	public LBool isInputSatisfiable() {
		return mSatisfiable;
	}

	public NestedFormulas<L, Term, Term> getAnnotatedSsa() {
		return mAnnotSSA;
	}

	private String getUniqueIdentifierForTestCaseName() {
		String identifier = "UnsatReuse" + mSSA.getTrace().hashCode();
		identifier += mSSA.getTrace().getSymbol(mSSA.getTrace().length() - 1).hashCode();
		return identifier;
	}

	private void getReuseCandidate() {
		// start after currentVA
		for (int i = mTrace.length() - 2; i > 0; i--) {
			if (mSSA.getTrace().getSymbol(i) instanceof StatementSequence) {
				final StatementSequence statementBranch = (StatementSequence) mSSA.getTrace().getSymbol(i);
				if (statementBranch.getPayload().getAnnotations()
						.containsKey(VarAssignmentReuseAnnotation.class.getName())) {
					final VarAssignmentReuseAnnotation reuseCandidate = (VarAssignmentReuseAnnotation) statementBranch
							.getPayload().getAnnotations().get(VarAssignmentReuseAnnotation.class.getName());
					if (!reuseCandidate.mVarAssignmentPair.isEmpty()) {
						mVAforReuse = reuseCandidate;
						mReuseCandidatePosition = i;
						break;
					} else {
						mVAforReuse = null;
					}
				}
			}
		}

	}

	private void ifStatementHasNondetAddToSet(final int i, final StatementSequence statementBranch) {
		if (!mTestGenReuseMode.equals(TestGenReuseMode.None)) {
			if (statementBranch.toString().contains("nondet")) {
				final Set<FunctionSymbol> nonTheorySymbolsInTerm =
						SmtUtils.extractNonTheoryFunctionSymbols(mSSA.getFormulaFromValidNonCallPos(i));

				for (final FunctionSymbol symbol : nonTheorySymbolsInTerm) {
					final Matcher m = Pattern.compile("__VERIFIER_nondet_(\\w*)")
							.matcher(statementBranch.getPayload().toString());
					if (m.find()) {
						if (symbol.getName().contains("nondet")) {
							nondetsInTrace.add(symbol.getName());
							nondetsInTraceAfterPreviousVA.add(symbol.getName());
							nondetNameToType.put(symbol.getName(), m.group(1));
						}
					}
				}
			}
		}
	}

	private ArrayList<Term> getNonDetsAsTermsReuse() {
		assert mTestGenReuseMode.equals(TestGenReuseMode.Reuse);
		final ArrayList<Term> nondetsAsTerms = new ArrayList<Term>();
		final ArrayList<Pair<Term, Term>> varAssignmentPairs = mVAforReuse.mVarAssignmentPair;
		for (int i = 0; i < varAssignmentPairs.size(); i++) { // TODO optimize in one loop over all nondets in trace
			// This "nondet" in Trace is in the VA
			final String nondetInVA = varAssignmentPairs.get(i).getFirst().toStringDirect();
			if (nondetsInTrace.contains(nondetInVA.substring(1, nondetInVA.length() - 1))) {
				final Term value = varAssignmentPairs.get(i).getSecond();
				final Term reuseVaTerm = createTermFromVA(varAssignmentPairs.get(i).getFirst().toStringDirect(), value);
				nondetsAsTerms.add(reuseVaTerm);
			}
		}
		return nondetsAsTerms;
	}

	private ArrayList<Term> getNonDetsAsTermsReuseUNSAT() {
		assert reuseUnsatpossible;
		final ArrayList<Term> nondetsAsTerms = new ArrayList<Term>();
		final ArrayList<Pair<Term, Term>> varAssignmentPairs = mVAforReuse.mVarAssignmentPair;

		boolean inputBetweenTestGoals = false;
		int nondetPositionCount = 0;
		final TestVector testV = new TestVector();

		for (final String nondet : nondetsInTrace) {
			boolean nondetNotInVA = true;
			Term value = null;
			for (int i = 0; i < varAssignmentPairs.size(); i++) { // TODO optimize in one loop over all nondets in trace
				// This "nondet" in Trace is in the VA
				if (varAssignmentPairs.get(i).getFirst().toStringDirect().contains(nondet)) {
					nondetNotInVA = false;
					value = varAssignmentPairs.get(i).getSecond();
					final Term reuseVaTerm =
							createTermFromVA(varAssignmentPairs.get(i).getFirst().toStringDirect(), value);
					nondetsAsTerms.add(reuseVaTerm);
					break;
				}
			}
			if (nondetNotInVA && nondetsInTraceAfterPreviousVA.contains(nondet) && reuseUnsatpossible) {
				// TODO verhindern, dass beim 2.checksat das hier nochmal gemacht wird!!

				// System.out.println("ALARM: " + nondet + " not in VA");
				inputBetweenTestGoals = true;
				value = null; // null will be used as value zero
				final Term reuseVaTerm = createTermFromVA(nondet, value);
				nondetsAsTerms.add(reuseVaTerm);
			}

			testV.addValueAssignment(value, nondetPositionCount, nondetNameToType.get(nondet));
			// increase at the end of loop
			nondetPositionCount += 1;
		}
		if (inputBetweenTestGoals) {
			exportTest(testV);
		}

		return nondetsAsTerms;

	}

	private void exportTest(final TestVector testV) {
		try {
			if (!testV.isEmpty()) {
				TestExporter.getInstance().exportTests(testV, getUniqueIdentifierForTestCaseName(), true);
			}
		} catch (final Exception e) {
			// TODO TestGeneration Auto-generated catch block
			e.printStackTrace();
		}
	}

	private void getCurrentVA() {
		final L lastStmt = mSSA.getTrace().getSymbol(mSSA.getTrace().length() - 1);
		if (lastStmt instanceof StatementSequence) {
			final StatementSequence lastStmtSeq = (StatementSequence) lastStmt;
			if (lastStmtSeq.getPayload().getAnnotations().containsKey(VarAssignmentReuseAnnotation.class.getName())) {
				mCurrentVA = (VarAssignmentReuseAnnotation) lastStmtSeq.getPayload().getAnnotations()
						.get(VarAssignmentReuseAnnotation.class.getName());
			}
		}
	}

	private void removeCheckIfCovered() {
		assert reuseUnsatpossible;
		if (mVAforReuse.mNegatedVA) {
			return;
		}
		if (mCurrentVA.mVAofOppositeBranch.mCoveredTestGoal) {
			return;
		}
		if (mVAforReuse.equals(mDefaultVA)) {
			System.out.println("OtherBranchRemoveCheckDefault");
			mCurrentVA.mVAofOppositeBranch.removeCheck();
			mCurrentVA.mVAofOppositeBranch.setVa(mValueAssignmentUsedForReuse, mHighestVaOrderInTrace,
					new ArrayList<VarAssignmentReuseAnnotation>());
			return;
		}

		// amount of nondets in VA + Between testgoals matches total amount of inputs
		assert nondetsInTrace.size() == nondetsInTraceAfterPreviousVA.size() + mVAforReuse.mVarAssignmentPair.size();
		System.out.println("OtherBranchRemoveCheck");
		mCurrentVA.mVAofOppositeBranch.removeCheck();
		mCurrentVA.mVAofOppositeBranch.setVa(mValueAssignmentUsedForReuse, mHighestVaOrderInTrace, mVAsInPrefix);

	}
}
