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
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.VarAssignmentReuseAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * TODO: use quick check
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
	// private VarAssignmentReuseAnnotation mVAforReuse = null; //For BitVec, since we have sort problem for a guess
	private VarAssignmentReuseAnnotation mVAforReuse; // Try to always use an VA,
														// if problem SORT maybe
														// just do it for int
	final LinkedHashSet<String> nondetsInTrace = new LinkedHashSet<String>();
	final HashMap<String, String> nondetNameToType = new HashMap<>();
	Integer mTestCaseUniqueIdentifier = 0;

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
	}

	public void buildAnnotatedSsaAndAssertTerms() {
		if (mAnnotSSA != null) {
			throw new AssertionError("already build");
		}
		assert mSatisfiable == null;

		mAnnotSSA = new ModifiableNestedFormulas<>(mTrace, new TreeMap<Integer, Term>());

		mAnnotSSA.setPrecondition(mAnnotateAndAssertCodeBlocks.annotateAndAssertPrecondition());
		mAnnotSSA.setPostcondition(mAnnotateAndAssertCodeBlocks.annotateAndAssertPostcondition());

		final Collection<Integer> callPositions = new ArrayList<>();
		final Collection<Integer> pendingReturnPositions = new ArrayList<>();
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
		VarAssignmentReuseAnnotation annotationOfCurrentTestGoal = null;
		final boolean reuseVarAssignmentsOfReachableErrorLocatiosn = true;
		final L lastStmt = mSSA.getTrace().getSymbol(mSSA.getTrace().length() - 1);

		if (lastStmt instanceof StatementSequence) {
			final StatementSequence lastStmtSeq = (StatementSequence) lastStmt;
			if (lastStmtSeq.getPayload().getAnnotations().containsKey(VarAssignmentReuseAnnotation.class.getName())) {

				annotationOfCurrentTestGoal = (VarAssignmentReuseAnnotation) lastStmtSeq.getPayload().getAnnotations()
						.get(VarAssignmentReuseAnnotation.class.getName());
			}
			System.out.println("HIER:  " + lastStmtSeq.getSerialNumber());
		}

		if (reuseVarAssignmentsOfReachableErrorLocatiosn) {
			boolean reuse = true;
			mVAforReuse = annotationOfCurrentTestGoal;
			checkTraceForVAandNONDETS();
			if (mVAforReuse != null) {
				final ArrayList<Pair<Term, Term>> varAssignmentPairs = mVAforReuse.mVarAssignmentPair;
				// TODO trying to reuse always if int
				if (nondetsInTrace.isEmpty() || annotationOfCurrentTestGoal.mUnsatWithVAs.contains(mVAforReuse)) {
					// // No Reuse
					System.out.println("NO REUSE");
					reuse = false;
				} else {
					System.out.println(varAssignmentPairs);
					reuse = true;
					final ArrayList<Term> vaPairsAsTerms = checkIfNondetsOfTraceAreInVA(); // TODO
					if (mVAforReuse.equals(annotationOfCurrentTestGoal)) {
						System.out.println("CURRENT VA is reused");
					}
					if (!vaPairsAsTerms.isEmpty() && reuse) { // TODO Needed?
						Term varAssignmentConjunction = SmtUtils.and(mMgdScriptTc.getScript(), vaPairsAsTerms);
						if (mVAforReuse.mIsNegated && !vaPairsAsTerms.isEmpty()) {
							varAssignmentConjunction = SmtUtils.not(mMgdScriptTc.getScript(), varAssignmentConjunction);
						}
						mMgdScriptTc.getScript().push(1);
						mAnnotateAndAssertCodeBlocks.annotateAndAssertTerm(varAssignmentConjunction, "Int");
						System.out.println("REUSE: " + varAssignmentConjunction);
					} else {
						reuse = false;
					}
				}
			}
			mSatisfiable = mMgdScriptTc.getScript().checkSat();
			if (mSatisfiable == LBool.UNSAT) {
				if (reuse) {
					annotationOfCurrentTestGoal.mUnsatWithVAs.add(mVAforReuse);
					// annotationOfCurrentTestGoal.mVAofOppositeBranch.setVa(mVAforReuse.mVarAssignmentPair);
					System.out.println("REUSE UNSAT");

					mMgdScriptTc.getScript().pop(1);
					annotationOfCurrentTestGoal.mVAofOppositeBranch.removeCheck();
				}
				// Hier oder vor der IF
				mSatisfiable = mMgdScriptTc.getScript().checkSat();
				if (mSatisfiable == LBool.SAT) {
					// TODO
					// register new model for 2nd check
					// annotationOfCurrentTestGoal.setVa(null);
				}
			} else if (reuse) {
				// register "other branch" as not reachable with this VA. Add negated VA to other branch test goal
				System.out.println("REUSE SUCCESSFULL");
				if (!mVAforReuse.equals(annotationOfCurrentTestGoal)) {
					annotationOfCurrentTestGoal.setVa(mVAforReuse.mVarAssignmentPair);
					if (mVAforReuse.mIsNegated) {
						// TODO Instead, VA with actual Model vor 2nd Check
						// mMgdScriptTc.getScript().getModel();
						// annotationOfCurrentTestGoal.negateVa(); //TODO ??? ACHTUNG DARF NICHT SEIN

					}
					if (annotationOfCurrentTestGoal.checkCount == 2) {
						mVAforReuse.negateVa();
					}

				}
				mSucessfulReuse = true;
			}
		} else {
			mSatisfiable = mMgdScriptTc.getScript().checkSat();
			// TODO no reuse, SAT, second checksat we can reuse
			// TODO guessed reuse UNSAT, checksat sat, we guess the same for second checksat instead of reusing
		}
		if (mSatisfiable == LBool.UNKNOWN) {
			System.out.println("UNKNOWN");
		}

		annotationOfCurrentTestGoal.checkCount += 1;

		// Report benchmarks
		mTcbg.reportNewCheckSat();
		mTcbg.reportNewCodeBlocks(mTrace.length());
		mTcbg.reportNewAssertedCodeBlocks(mTrace.length());
		mLogger.info("Conjunction of SSA is " + mSatisfiable);
	}

	private Term createTermFromVA(final String variableAsString, final Term value) {
		final FunctionSymbol varInCurrentScript = mMgdScriptTc.getScript().getTheory()
				.getFunction(variableAsString.substring(1, variableAsString.length() - 1));
		System.out.println(variableAsString);
		if (varInCurrentScript == null) {
			throw new AssertionError("unknown var " + variableAsString);
		}

		final Term nondetVar = SmtUtils.unfTerm(mMgdScriptTc.getScript(), varInCurrentScript);

		final Term nondetValue;

		switch (nondetVar.getSort().getName()) {
		case SmtSortUtils.FLOATINGPOINT_SORT: {
			if (value != null) {
				final ApplicationTerm valueAsAppterm = (ApplicationTerm) value;
				nondetValue = SmtUtils.unfTerm(mMgdScriptTc.getScript(), valueAsAppterm.getFunction().getName(), null,
						null, valueAsAppterm.getParameters());
			} else {
				throw new AssertionError("TODO FLOATINGPOINT_SORT Default vlaue ");
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
		default: {
			nondetValue = SmtUtils.constructIntegerValue(mMgdScriptTc.getScript(),
					SmtSortUtils.getIntSort(mMgdScriptTc), BigInteger.ZERO);
			break;
		}
		}
		return SmtUtils.binaryEquality(mMgdScriptTc.getScript(), nondetVar, nondetValue);
	}

	public LBool isInputSatisfiable() {
		return mSatisfiable;
	}

	public NestedFormulas<L, Term, Term> getAnnotatedSsa() {
		return mAnnotSSA;
	}

	/*
	 * Iterates over trace and returns last VA and all Nondets in trace
	 */
	private void checkTraceForVAandNONDETS() {
		mTestCaseUniqueIdentifier = mSSA.getTrace().hashCode();
		if (mSSA.getTrace().length() - 1 > 0) {
			for (int i = 0; i < mSSA.getTrace().length() - 1; i++) { // dont check current testgoal for va
				if (mSSA.getTrace().getSymbol(i) instanceof StatementSequence) {
					final StatementSequence statementBranch = (StatementSequence) mSSA.getTrace().getSymbol(i);

					if (statementBranch.toString().startsWith("havoc")
							&& statementBranch.toString().contains("nondet")) {
						final String traceTermAsString = mSSA.getFormulaFromNonCallPos(i).toStringDirect();
						final Pattern pattern = Pattern.compile("\\|.*nondet\\d[^\\|]*\\|", Pattern.CASE_INSENSITIVE);
						final Matcher matcher = pattern.matcher(traceTermAsString);
						if (matcher.find()) {
							final String match = matcher.group();
							nondetsInTrace.add(match.toString());
							nondetNameToType.put(match.toString(),
									TestVector.getNonDetTypeFromName(statementBranch.getPayload().toString()));
						}

					}
					// If VA in Trace returns last found VA
					if (statementBranch.getPayload().getAnnotations()
							.containsKey(VarAssignmentReuseAnnotation.class.getName())) {
						mVAforReuse = (VarAssignmentReuseAnnotation) statementBranch.getPayload().getAnnotations()
								.get(VarAssignmentReuseAnnotation.class.getName());
					}
				}
			}
		}

	}

	/*
	 * Checks wheter a nondet from the trace is in the VA or not.
	 * IF it is included it is in the first array list and otherwise in the second of PAIR
	 */
	private ArrayList<Term> checkIfNondetsOfTraceAreInVA() {
		final ArrayList<Pair<Term, Term>> varAssignmentPairs = mVAforReuse.mVarAssignmentPair;
		final ArrayList<Term> nondetInVA = new ArrayList<Term>();
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
					nondetInVA.add(reuseVaTerm);
					break;
				}
			}

			if (nondetNotInVA) {
				// TODO verhindern, dass beim 2.checksat das hier nochmal gemacht wird!!
				System.out.println("ALARM: " + nondet + " not in VA");
				inputBetweenTestGoals = true;
				value = null; // null will be used as value zero
				final Term reuseVaTerm = createTermFromVA(nondet, value);
				nondetInVA.add(reuseVaTerm);
			}

			testV.addValueAssignment(value, nondetPositionCount, nondetNameToType.get(nondet));
			// increase at the end of loop
			nondetPositionCount += 1;
		}
		if (inputBetweenTestGoals && mVAforReuse.checkCount == 2) {
			exportTest(testV);
		}
		return nondetInVA;
	}

	private void exportTest(final TestVector testV) {
		try {
			if (!testV.isEmpty()) {
				TestExporter.getInstance().exportTests(testV, mTestCaseUniqueIdentifier, true);
			}
		} catch (final Exception e) {
			// TODO TestGeneration Auto-generated catch block
			e.printStackTrace();
		}
	}
}
