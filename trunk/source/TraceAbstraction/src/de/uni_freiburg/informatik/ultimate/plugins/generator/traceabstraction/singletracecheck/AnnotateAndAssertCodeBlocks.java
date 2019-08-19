/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheck.TraceCheckLock;

/**
 * Annotate formulas of SSA (e.g., with ssa_{42}) and assert them.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class AnnotateAndAssertCodeBlocks {

	protected final ILogger mLogger;

	protected final Script mScript;
	protected final ManagedScript mMgdScript;
	protected final Object mScriptLockOwner;
	protected final NestedWord<? extends IAction> mTrace;

	protected LBool mSatisfiable;
	protected final NestedFormulas<Term, Term> mSSA;
	protected ModifiableNestedFormulas<Term, Term> mAnnotSSA;

	protected static final String SSA = "ssa_";
	protected static final String PRECOND = "precond";
	protected static final String POSTCOND = "postcond";
	protected static final String RETURN = "_return";
	protected static final String LOCVARASSIGN_CALL = "_LocVarAssigCall";
	protected static final String GLOBVARASSIGN_CALL = "_GlobVarAssigCall";
	protected static final String OLDVARASSIGN_CALL = "_OldVarAssigCall";
	protected static final String PENDINGCONTEXT = "_PendingContext";
	protected static final String LOCVARASSIGN_PENDINGCONTEXT = "_LocVarAssignPendingContext";
	protected static final String OLDVARASSIGN_PENDINGCONTEXT = "_OldVarAssignPendingContext";

	public AnnotateAndAssertCodeBlocks(final ManagedScript csToolkit, final TraceCheckLock scriptLockOwner,
			final NestedFormulas<Term, Term> nestedSSA, final ILogger logger) {
		mLogger = logger;
		mMgdScript = csToolkit;
		mScriptLockOwner = scriptLockOwner;
		mScript = csToolkit.getScript();
		mTrace = nestedSSA.getTrace();
		mSSA = nestedSSA;
	}

	protected Term annotateAndAssertPrecondition() {
		final String name = precondAnnotation();
		final Term annotated = annotateAndAssertTerm(mSSA.getPrecondition(), name);
		return annotated;
	}

	protected String precondAnnotation() {
		return SSA + PRECOND;
	}

	protected Term annotateAndAssertPostcondition() {
		final String name = postcondAnnotation();
		final Term negatedPostcondition = mScript.term("not", mSSA.getPostcondition());
		final Term annotated = annotateAndAssertTerm(negatedPostcondition, name);
		return annotated;
	}

	protected String postcondAnnotation() {
		return SSA + POSTCOND;
	}

	protected Term annotateAndAssertNonCall(final int position) {
		String name;
		if (mTrace.isReturnPosition(position)) {
			name = returnAnnotation(position);
		} else {
			name = internalAnnotation(position);
		}
		final Term original = mSSA.getFormulaFromNonCallPos(position);
		final Term annotated = annotateAndAssertTerm(original, name);
		return annotated;
	}

	protected String internalAnnotation(final int position) {
		return SSA + position;
	}

	protected String returnAnnotation(final int position) {
		return SSA + position + RETURN;
	}

	protected Term annotateAndAssertLocalVarAssignemntCall(final int position) {
		final String name = localVarAssignemntCallAnnotation(position);
		final Term indexed = mSSA.getLocalVarAssignment(position);
		final Term annotated = annotateAndAssertTerm(indexed, name);
		return annotated;
	}

	protected String localVarAssignemntCallAnnotation(final int position) {
		return SSA + position + LOCVARASSIGN_CALL;
	}

	protected Term annotateAndAssertGlobalVarAssignemntCall(final int position) {
		final String name = globalVarAssignemntAnnotation(position);
		final Term indexed = mSSA.getGlobalVarAssignment(position);
		final Term annotated = annotateAndAssertTerm(indexed, name);
		return annotated;
	}

	protected String globalVarAssignemntAnnotation(final int position) {
		return SSA + position + GLOBVARASSIGN_CALL;
	}

	protected Term annotateAndAssertOldVarAssignemntCall(final int position) {
		final String name = oldVarAssignemntCallAnnotation(position);
		final Term indexed = mSSA.getOldVarAssignment(position);
		final Term annotated = annotateAndAssertTerm(indexed, name);
		return annotated;
	}

	protected String oldVarAssignemntCallAnnotation(final int position) {
		return SSA + position + OLDVARASSIGN_CALL;
	}

	protected Term annotateAndAssertPendingContext(final int positionOfPendingContext, final int pendingContextCode) {
		final String name = pendingContextAnnotation(pendingContextCode);
		final Term indexed = mSSA.getPendingContext(positionOfPendingContext);
		final Term annotated = annotateAndAssertTerm(indexed, name);
		return annotated;
	}

	protected String pendingContextAnnotation(final int pendingContextCode) {
		return SSA + pendingContextCode + PENDINGCONTEXT;
	}

	protected Term annotateAndAssertLocalVarAssignemntPendingContext(final int positionOfPendingReturn,
			final int pendingContextCode) {
		final String name = localVarAssignemntPendingReturnAnnotation(pendingContextCode);
		final Term indexed = mSSA.getLocalVarAssignment(positionOfPendingReturn);
		final Term annotated = annotateAndAssertTerm(indexed, name);
		return annotated;
	}

	protected String localVarAssignemntPendingReturnAnnotation(final int pendingContextCode) {
		return SSA + pendingContextCode + LOCVARASSIGN_PENDINGCONTEXT;
	}

	protected Term annotateAndAssertOldVarAssignemntPendingContext(final int positionOfPendingReturn,
			final int pendingContextCode) {
		final String name = oldVarAssignemntPendingReturnAnnotation(pendingContextCode);
		final Term indexed = mSSA.getOldVarAssignment(positionOfPendingReturn);
		final Term annotated = annotateAndAssertTerm(indexed, name);
		return annotated;
	}

	protected String oldVarAssignemntPendingReturnAnnotation(final int pendingContextCode) {
		return SSA + pendingContextCode + OLDVARASSIGN_PENDINGCONTEXT;
	}

	protected Term annotateAndAssertTerm(final Term term, final String name) {
		assert term.getFreeVars().length == 0 : "Term has free vars";
		final Annotation annot = new Annotation(":named", name);
		final Term annotTerm = mScript.annotate(term, annot);
		mMgdScript.assertTerm(mScriptLockOwner, annotTerm);
		final Term constantRepresentingAnnotatedTerm = mScript.term(name);
		return constantRepresentingAnnotatedTerm;
	}

	/**
	 * Represents one conjunct in an annoted SSA. The annotated term is the term submitted to the solver (we have to use
	 * these named terms in order to obtain an unsatisfiable core).
	 *
	 */
	public static class AnnotatedSsaConjunct {
		private final Term mAnnotedTerm;
		private final Term mOriginalTerm;

		public AnnotatedSsaConjunct(final Term annotedTerm, final Term originalTerm) {
			super();
			mAnnotedTerm = annotedTerm;
			mOriginalTerm = originalTerm;
		}

		public Term getAnnotedTerm() {
			return mAnnotedTerm;
		}

		public Term getOriginalTerm() {
			return mOriginalTerm;
		}

		@Override
		public String toString() {
			return "AnnotatedSsaConjunct [mAnnotedTerm=" + mAnnotedTerm + ", mOriginalTerm=" + mOriginalTerm + "]";
		}

	}
}
