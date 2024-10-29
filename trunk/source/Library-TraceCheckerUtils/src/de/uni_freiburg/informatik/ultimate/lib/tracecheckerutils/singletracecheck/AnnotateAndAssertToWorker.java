package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheck.TraceCheckLock;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class AnnotateAndAssertToWorker<L extends IAction> extends AnnotateAndAssertConjunctsOfCodeBlocks<L> {

	final TermTransferrer mTf;

	/*
	 * Does the same as AnnotateAndAssertConjunctsOfCodeBlocks
	 * But, everything we get from the nestedSSA will go through termtransferrrer
	 * who transfers from main to worker script
	 */
	public AnnotateAndAssertToWorker(final ManagedScript mgdScriptTc, final TraceCheckLock scriptLockOwner,
			final NestedFormulas<L, Term, Term> nestedSSA,
			final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> nestedFormulas, final ILogger logger,
			final ManagedScript mgdScriptCfg) {
		super(mgdScriptTc, scriptLockOwner, nestedSSA, nestedFormulas, logger, mgdScriptCfg);
		// This class should only be called from a worker
		assert ((HistoryRecordingScript) mMgdScript.getScript()).getMainScript() != null;
		mTf = new TermTransferrer(((HistoryRecordingScript) mMgdScript.getScript()).getMainScript().getScript(),
				mMgdScript.getScript());
	}

	@Override
	protected Term annotateAndAssertPrecondition() {
		final String name = super.precondAnnotation();
		final Term original = mNestedFormulas.getPrecondition().getFormula();
		final Term indexed = mTf.transform(mSSA.getPrecondition());
		return super.annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertPostcondition() {
		final String name = super.postcondAnnotation();
		final Term original = mNestedFormulas.getPostcondition().getFormula();
		final Term indexed = mScript.term("not", mTf.transform(mSSA.getPostcondition()));
		return super.annotateAndAssertConjunction(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertNonCall(final int position) {
		String name;
		if (mTrace.isReturnPosition(position)) {
			name = returnAnnotation(position);
		} else {
			name = internalAnnotation(position);
		}

		final Term original = mNestedFormulas.getFormulaFromNonCallPos(position).getFormula();
		final Term indexed = mTf.transform(mSSA.getFormulaFromNonCallPos(position));
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertLocalVarAssignemntCall(final int position) {
		final String name = super.localVarAssignemntCallAnnotation(position);
		final Term original = mNestedFormulas.getLocalVarAssignment(position).getFormula();
		final Term indexed = mTf.transform(mSSA.getLocalVarAssignment(position));
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertGlobalVarAssignemntCall(final int position) {
		final String name = super.globalVarAssignemntAnnotation(position);
		final Term original = mNestedFormulas.getGlobalVarAssignment(position).getFormula();
		final Term indexed = mTf.transform(mSSA.getGlobalVarAssignment(position));
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertOldVarAssignemntCall(final int position) {
		final String name = super.oldVarAssignemntCallAnnotation(position);
		final Term original = mNestedFormulas.getOldVarAssignment(position).getFormula();
		final Term indexed = mTf.transform(mSSA.getOldVarAssignment(position));
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertPendingContext(final int positionOfPendingContext, final int pendingContextCode) {
		final String name = super.pendingContextAnnotation(pendingContextCode);
		final Term original = mNestedFormulas.getPendingContext(positionOfPendingContext).getFormula();
		final Term indexed = mTf.transform(mSSA.getPendingContext(positionOfPendingContext));
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertLocalVarAssignemntPendingContext(final int positionOfPendingReturn,
			final int pendingContextCode) {
		final String name = super.localVarAssignemntPendingReturnAnnotation(pendingContextCode);
		final Term original = mNestedFormulas.getLocalVarAssignment(positionOfPendingReturn).getFormula();
		final Term indexed = mTf.transform(mSSA.getLocalVarAssignment(positionOfPendingReturn));
		return annotateAndAssertConjuncts(name, original, indexed);
	}

	@Override
	protected Term annotateAndAssertOldVarAssignemntPendingContext(final int positionOfPendingReturn,
			final int pendingContextCode) {
		final String name = super.oldVarAssignemntPendingReturnAnnotation(pendingContextCode);
		final Term original = mNestedFormulas.getOldVarAssignment(positionOfPendingReturn).getFormula();
		final Term indexed = mTf.transform(mSSA.getOldVarAssignment(positionOfPendingReturn));
		return annotateAndAssertConjuncts(name, original, indexed);
	}
}
