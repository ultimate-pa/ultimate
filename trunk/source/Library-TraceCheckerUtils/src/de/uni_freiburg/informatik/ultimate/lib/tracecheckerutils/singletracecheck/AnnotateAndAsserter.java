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
import java.util.LinkedHashSet;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.VarAssignmentReuseAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
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
		}
		boolean nondetBetweenTestGoals = false;
		if (reuseVarAssignmentsOfReachableErrorLocatiosn) {

			boolean reuse = false;
			final Pair<VarAssignmentReuseAnnotation, LinkedHashSet<String>> todoname = checkTraceForVAandNONDETS();
			if (todoname.getFirst() != null) {
				final ArrayList<Pair<Term, Term>> varAssignmentPairs = todoname.getFirst().mVarAssignmentPair;
				if (varAssignmentPairs.isEmpty() || todoname.getSecond().isEmpty()) {
					// No Reuse
					System.out.println("NO REUSE");
				} else {
					System.out.println(varAssignmentPairs);
					reuse = true;
					System.out.println("REUSE");
					final ArrayList<Term> termsFromVAs = new ArrayList<Term>();
					for (final String nondet : todoname.getSecond()) {
						boolean nondetNotInVA = true;
						for (int i = 0; i < varAssignmentPairs.size(); i++) {
							// remove after debugging
							if (mMgdScriptTc.getScript().getTheory()
									.getFunction(varAssignmentPairs.get(i).getFirst().toStringDirect().substring(1,
											varAssignmentPairs.get(i).getFirst().toStringDirect().length()
													- 1)) == null) {

								throw new AssertionError("ALARMAPAMAA");

							}

							// For this nondet in Trace we do not have an entry in the VA
							if (varAssignmentPairs.get(i).getFirst().toStringDirect().contains(nondet)) {
								nondetNotInVA = false;
								final Term reuseVaTerm = createTermFromVA(varAssignmentPairs.get(i).getFirst(),
										varAssignmentPairs.get(i).getSecond());
								termsFromVAs.add(reuseVaTerm);
							}
						}
						if (nondetNotInVA) {
							System.out.println("ALARM: " + nondet + "not in VA");

							nondetBetweenTestGoals = true;

							// TODO create a term somehow lmao
							// termsFromVAs.add();
							// final Term reuseVaTerm = createTermForNondetNotInVa();
							// termsFromVAs.add(reuseVaTerm);
						}
					}
					if (!termsFromVAs.isEmpty()) { // TODO Needed?
						Term varAssignmentConjunction = SmtUtils.and(mMgdScriptTc.getScript(), termsFromVAs);
						if (todoname.getFirst().mIsNegated && !termsFromVAs.isEmpty()) {
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
					// TODO register "other branch" as reached by VA !!!!!!ACHRUNG CURREN TBRANCH NCIHT WIE HIER
					// new VA will be added in trace check //TODO are you sure?
					System.out.println("REUSE UNSAT");
					if (!nondetBetweenTestGoals) {
						annotationOfCurrentTestGoal.mVAofOppositeBranch.removeCheck();
					}
					annotationOfCurrentTestGoal.mVAofOppositeBranch
							.setVa(annotationOfCurrentTestGoal.mVarAssignmentPair);
					// TODO VA annotate to opposite branch.
					// if no nondet in between, copy from old else add new
					mMgdScriptTc.getScript().pop(1);
				}
				// Hier oder vor der IF
				mSatisfiable = mMgdScriptTc.getScript().checkSat();
			} else if (reuse) {
				// register "other branch" as not reachable with this VA. Add negated VA to other branch test goal
				System.out.println("REUSE SUCCESSFULL");
				todoname.getFirst().negateVa();
				mSucessfulReuse = true;
			}
		} else {
			mSatisfiable = mMgdScriptTc.getScript().checkSat();
		}
		if (mSatisfiable == LBool.UNKNOWN) {
			System.out.println("UNKNOWN");
		}
		// Report benchmarks
		mTcbg.reportNewCheckSat();
		mTcbg.reportNewCodeBlocks(mTrace.length());
		mTcbg.reportNewAssertedCodeBlocks(mTrace.length());
		mLogger.info("Conjunction of SSA is " + mSatisfiable);
	}

	private Term createTermFromVA(final Term variable, final Term value) {
		final FunctionSymbol varInCurrentScript = mMgdScriptTc.getScript().getTheory()
				.getFunction(variable.toStringDirect().substring(1, variable.toStringDirect().length() - 1));
		if (varInCurrentScript == null) {
			System.out.println(variable);
			throw new AssertionError("unknown var " + variable);
		}

		final Term nondetVar = SmtUtils.unfTerm(mMgdScriptTc.getScript(), varInCurrentScript);

		Term nondetValue = value;
		switch (nondetVar.getSort().getName()) {
		case SmtSortUtils.FLOATINGPOINT_SORT: {

			final ApplicationTerm valueAsAppterm = (ApplicationTerm) value;

			nondetValue = SmtUtils.unfTerm(mMgdScriptTc.getScript(), valueAsAppterm.getFunction().getName(), null, null,
					valueAsAppterm.getParameters());
			break;
		}
		case SmtSortUtils.BITVECTOR_SORT: {
			final ApplicationTerm valueAsAppterm = (ApplicationTerm) value;

			final BigInteger constValue = new BigInteger(valueAsAppterm.getFunction().getName().substring(2));
			nondetValue = BitvectorUtils.constructTerm(mMgdScriptTc.getScript(),
					BitvectorUtils.constructBitvectorConstant(constValue, nondetVar.getSort()));

			break;
		}
		default: {
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

	private Pair<VarAssignmentReuseAnnotation, LinkedHashSet<String>> checkTraceForVAandNONDETS() {
		VarAssignmentReuseAnnotation vaAnnotation = null;
		final LinkedHashSet<String> nondetsInTrace = new LinkedHashSet<String>();
		if (mSSA.getTrace().length() - 1 > 0) {
			for (int i = 0; i < mSSA.getTrace().length() - 1; i++) { // dont check current testgoal for va
				if (mSSA.getTrace().getSymbol(i) instanceof StatementSequence) {
					final StatementSequence statementBranch = (StatementSequence) mSSA.getTrace().getSymbol(i);
					// If Nondet in Trace add to Set
					if (statementBranch.toString().startsWith("havoc")
							&& statementBranch.toString().contains("nondet")) {
						// TODO only one entry per nondet!!!!! bestcase already remove unnecessary chars

						for (final IProgramVar var : statementBranch.getTransformula().getAssignedVars()) {
							statementBranch.getTransformula().getAssignedVars().toString();
							final Pattern pattern = Pattern.compile("nondet\\d+", Pattern.CASE_INSENSITIVE);
							final Matcher matcher = pattern.matcher(var.toString());

							if (matcher.find()) {
								final String match = matcher.group();
								nondetsInTrace.add(var.toString());
							}

						}

					}
					// If VA in Trace returns last found VA
					if (statementBranch.getPayload().getAnnotations()
							.containsKey(VarAssignmentReuseAnnotation.class.getName())) {
						vaAnnotation = (VarAssignmentReuseAnnotation) statementBranch.getPayload().getAnnotations()
								.get(VarAssignmentReuseAnnotation.class.getName());
					}
				}
			}
		}
		return new Pair<>(vaAnnotation, nondetsInTrace);
	}

}
