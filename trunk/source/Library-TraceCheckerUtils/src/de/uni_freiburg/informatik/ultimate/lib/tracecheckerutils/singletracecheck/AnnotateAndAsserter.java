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

import java.util.ArrayList;
import java.util.Collection;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.VarAssignmentReuseAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.TraceCheckerUtils;
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
		final boolean reuseVarAssignmentsOfReachableErrorLocatiosn = true;
		ArrayList<Pair<Term, Term>> varAssignmentPair = new ArrayList<Pair<Term, Term>>();

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
			if (reuseVarAssignmentsOfReachableErrorLocatiosn) {
				System.out.println(mSSA.getTrace().getSymbol(positionOfPendingReturn));
			}
		}

		if (reuseVarAssignmentsOfReachableErrorLocatiosn) {
			// final IPredicate errorStatePredecessor =
			// (IPredicate) mSSA.getTrace().getSymbol(mSSA.getTrace().length() - 2);
			// final ISLPredicate test = (ISLPredicate) errorStatePredecessor;

			boolean reuse = false;
			VarAssignmentReuseAnnotation vaAnnotation = null;
			// TODO check mSSA.getTrace().length() - 1 > 0
			if (mSSA.getTrace().length() - 1 > 0) {
				for (int i = 0; i < mSSA.getTrace().length() - 1; i++) { // dont check current testgoal for va
					if (mSSA.getTrace().getSymbol(i) instanceof StatementSequence) {
						final StatementSequence statementBranch = (StatementSequence) mSSA.getTrace().getSymbol(i);
						if (statementBranch.getPayload().getAnnotations()
								.containsKey(VarAssignmentReuseAnnotation.class.getName())) {
							vaAnnotation = (VarAssignmentReuseAnnotation) statementBranch.getPayload().getAnnotations()
									.get(VarAssignmentReuseAnnotation.class.getName());
							varAssignmentPair = vaAnnotation.mVarAssignmentPair;
							if (!vaAnnotation.mVarAssignmentPair.isEmpty()) {
								reuse = true;
							} else {
								// TODO muss so sein wenn wir schlüsse auf else branch schließen wollen.
								// Weil das ist die garantie, dass keine termination dazwischen stattfinden kann
								// Wichtig dass wir nicht auf false setzten wenn wir hier das aktuelle testgoal lesen
								reuse = false;
							}
						}
						// if new input in trace. Set value for input and assert it.
						// Create testcase with this value and the rest of the VA
					}
				}
			}
			if (reuse && vaAnnotation != null) { // ensure arraylist not empty
				mMgdScriptTc.getScript().push(1); // Push und pop muss wo anders passieren, sonst ist das model weg
													// in
													// einem
				final ArrayList<Term> andVa = new ArrayList<Term>();
				for (int i = 0; i < varAssignmentPair.size(); i++) {
					varAssignmentPair.get(i);
					if (mMgdScriptTc.getScript().getTheory()
							.getFunction(varAssignmentPair.get(i).getFirst().toStringDirect().substring(1,
									varAssignmentPair.get(i).getFirst().toStringDirect().length() - 1)) == null) {
						System.out.println("TODO" + varAssignmentPair.get(i).getFirst().toStringDirect());
						System.out.println(mMgdScriptTc.getScript().getTheory()
								.getFunction(varAssignmentPair.get(i).getFirst().toStringDirect().substring(1,
										varAssignmentPair.get(i).getFirst().toStringDirect().length() - 1)));
						reuse = false;
					} else {

						final Term nondetVar = SmtUtils.unfTerm(mMgdScriptTc.getScript(),
								mMgdScriptTc.getScript().getTheory()
										.getFunction(varAssignmentPair.get(i).getFirst().toStringDirect().substring(1,
												varAssignmentPair.get(i).getFirst().toStringDirect().length() - 1)));
						andVa.add(SmtUtils.binaryEquality(mMgdScriptTc.getScript(), nondetVar,
								varAssignmentPair.get(i).getSecond()));
					}
				}

				Term varAssignmentConjunction = SmtUtils.and(mMgdScriptTc.getScript(), andVa);
				if (vaAnnotation.mIsNegated && !andVa.isEmpty()) {
					varAssignmentConjunction = SmtUtils.not(mMgdScriptTc.getScript(), varAssignmentConjunction);
					// TODO evaluate if negated reuse is helpfull
					mAnnotateAndAssertCodeBlocks.annotateAndAssertTerm(varAssignmentConjunction, "Int");
					System.out.println("REUSE: " + varAssignmentConjunction);
				} else {
					mAnnotateAndAssertCodeBlocks.annotateAndAssertTerm(varAssignmentConjunction, "Int");
					System.out.println("REUSE: " + varAssignmentConjunction);
				}

			}
			mSatisfiable = mMgdScriptTc.getScript().checkSat();
			if (!reuse) {
				System.out.println("NO REUSE");
			} else {
				System.out.println("REUSE");
			}
			if (mSatisfiable == LBool.UNSAT) {
				if (reuse) {
					// register "other branch" as reached by VA
					// new VA will be added in trace check
					System.out.println("REUSE UNSAT");
					vaAnnotation.mVAofOppositeBranch.removeCheck();
					vaAnnotation.negateVa();
					mMgdScriptTc.getScript().pop(1);
				}
				// Hier oder vor der IF
				mSatisfiable = mMgdScriptTc.getScript().checkSat();
			} else if (reuse) {
				// register "other branch" as not reachable with this VA. Add negated VA to other branch test goal
				System.out.println("REUSE SUCCESSFULL");
				vaAnnotation.mVAofOppositeBranch.negateVa();
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

	public LBool isInputSatisfiable() {
		return mSatisfiable;
	}

	public NestedFormulas<L, Term, Term> getAnnotatedSsa() {
		return mAnnotSSA;
	}
}
