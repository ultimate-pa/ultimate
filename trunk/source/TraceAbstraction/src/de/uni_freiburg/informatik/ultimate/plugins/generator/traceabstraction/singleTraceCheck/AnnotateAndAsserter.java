/*
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker.TraceCheckerBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;


/**
 * TODO: use quick check
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class AnnotateAndAsserter {
	
	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;

	protected final ManagedScript mMgdScriptTc;
	protected final NestedWord<? extends IAction> mTrace;


	protected LBool mSatisfiable;
	protected final NestedFormulas<Term, Term> mSSA;
	protected ModifiableNestedFormulas<Term, Term> mAnnotSSA;

	protected final AnnotateAndAssertCodeBlocks mAnnotateAndAssertCodeBlocks;

	protected final TraceCheckerBenchmarkGenerator mTcbg;

	public AnnotateAndAsserter(final ManagedScript mgdScriptTc,
			final NestedFormulas<Term, Term> nestedSSA, 
			final AnnotateAndAssertCodeBlocks aaacb, 
			final TraceCheckerBenchmarkGenerator tcbg, final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
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

		mAnnotSSA = new ModifiableNestedFormulas<Term, Term>(mTrace, new TreeMap<Integer, Term>());

		mAnnotSSA.setPrecondition(mAnnotateAndAssertCodeBlocks.annotateAndAssertPrecondition());
		mAnnotSSA.setPostcondition(mAnnotateAndAssertCodeBlocks.annotateAndAssertPostcondition());

		final Collection<Integer> callPositions = new ArrayList<Integer>();
		final Collection<Integer> pendingReturnPositions = new ArrayList<Integer>();
		for (int i=0; i<mTrace.length(); i++) {
			if (mTrace.isCallPosition(i)) {
				callPositions.add(i);
				mAnnotSSA.setGlobalVarAssignmentAtPos(i, mAnnotateAndAssertCodeBlocks.annotateAndAssertGlobalVarAssignemntCall(i));
				mAnnotSSA.setLocalVarAssignmentAtPos(i, mAnnotateAndAssertCodeBlocks.annotateAndAssertLocalVarAssignemntCall(i));
				mAnnotSSA.setOldVarAssignmentAtPos(i, mAnnotateAndAssertCodeBlocks.annotateAndAssertOldVarAssignemntCall(i));
			} else  {
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
				final Term annotated = mAnnotateAndAssertCodeBlocks.annotateAndAssertPendingContext(
						positionOfPendingReturn, pendingContextCode);
				mAnnotSSA.setPendingContext(positionOfPendingReturn, annotated);
			}
			{
				final Term annotated = mAnnotateAndAssertCodeBlocks.annotateAndAssertLocalVarAssignemntPendingContext(
						positionOfPendingReturn, pendingContextCode);
				mAnnotSSA.setLocalVarAssignmentAtPos(positionOfPendingReturn, annotated);
			}
			{
				final Term annotated = mAnnotateAndAssertCodeBlocks.annotateAndAssertOldVarAssignemntPendingContext(
						positionOfPendingReturn, pendingContextCode);
				mAnnotSSA.setOldVarAssignmentAtPos(positionOfPendingReturn, annotated);
			}
			pendingContextCode++;
		}
		try {
			mSatisfiable = mMgdScriptTc.getScript().checkSat();
		} catch (final SMTLIBException e) {
			if (e.getMessage().contains("Received EOF on stdin. No stderr output.")
					&& !mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(getClass(), 
						"checking feasibility of error trace whose length is " + mTrace.length());
			} else {
				throw e;
			}
		}
		// Report benchmarks
		mTcbg.reportnewCheckSat();
		mTcbg.reportnewCodeBlocks(mTrace.length());
		mTcbg.reportnewAssertedCodeBlocks(mTrace.length());
		mLogger.info("Conjunction of SSA is " + mSatisfiable);
	}



	public LBool isInputSatisfiable() {
		return mSatisfiable;
	}




	/**
	 * Return a ParallelComposition-free trace of a trace.
	 * While using large block encoding this sequence is not unique.
	 * @param smtManager <ul>
	 * <li> If smtManager is null some branch of a ParallelComposition is taken.
	 * <li> If smtManager is not null, the smtManger has to be a state where a
	 * valuation of this traces branch indicators is available. Then some branch
	 * for which the branch indicator evaluates to true is taken.
	 */
	public static List<CodeBlock> constructFailureTrace(
			final Word<CodeBlock> word, final SmtManager smtManager) {
		final List<CodeBlock> failurePath = new ArrayList<CodeBlock>();
		for (int i=0; i<word.length(); i++) {
			final CodeBlock codeBlock = word.getSymbol(i);
			addToFailureTrace(codeBlock, i , failurePath, smtManager);
		}
		return failurePath;
	}

	/**
	 * Recursive method used by getFailurePath
	 */
	private static void addToFailureTrace(final CodeBlock codeBlock, final int pos, 
			final List<CodeBlock> failureTrace, final SmtManager smtManager) {
		if (codeBlock instanceof Call) {
			failureTrace.add(codeBlock);
		} else if (codeBlock instanceof Return) {
			failureTrace.add(codeBlock);
		} else if (codeBlock instanceof Summary) {
			failureTrace.add(codeBlock);
		} else if (codeBlock instanceof StatementSequence) {
			failureTrace.add(codeBlock);
		} else if (codeBlock instanceof SequentialComposition) {
			final SequentialComposition seqComp = (SequentialComposition) codeBlock;
			for (final CodeBlock elem : seqComp.getCodeBlocks()) {
				addToFailureTrace(elem, pos, failureTrace, smtManager);
			}
		} else if (codeBlock instanceof ParallelComposition) {
			final ParallelComposition parComp = (ParallelComposition) codeBlock;

			final Set<TermVariable> branchIndicators = parComp.getBranchIndicator2CodeBlock().keySet();

			TermVariable taken = null;

			if (smtManager == null) {
				// take some branch
				taken = branchIndicators.iterator().next();
			}
			else {
				// take some branch for which the branch indicator evaluates to
				// true
				for (final TermVariable tv : branchIndicators) {
					final String constantName = tv.getName()+"_"+pos;
					final Term constant = smtManager.getScript().term(constantName);
					final Term[] terms = { constant };
					final Map<Term, Term> valuation = smtManager.getScript().getValue(terms);
					final Term value = valuation.get(constant);
					if (value == smtManager.getScript().term("true")) {
						taken = tv;
					}
				}
			}
			assert (taken != null);
			final CodeBlock cb = parComp.getBranchIndicator2CodeBlock().get(taken); 
			addToFailureTrace(cb, pos, failureTrace, smtManager);
		} else {
			throw new IllegalArgumentException("unkown code block");
		}
	}


	public NestedFormulas<Term, Term> getAnnotatedSsa() {
		return mAnnotSSA;
	}



}
