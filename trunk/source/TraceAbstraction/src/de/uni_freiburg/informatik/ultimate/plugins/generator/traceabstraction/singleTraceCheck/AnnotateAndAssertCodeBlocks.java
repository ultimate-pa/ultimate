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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IAction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * Annotate formulas of SSA (e.g., with ssa_{42}) and assert them.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class AnnotateAndAssertCodeBlocks {

	protected final ILogger mLogger;

	protected final Script m_Script;
	protected final SmtManager m_SmtManager;
	protected final NestedWord<? extends IAction> m_Trace;

	protected LBool m_Satisfiable;
	protected final NestedFormulas<Term, Term> m_SSA;
	protected ModifiableNestedFormulas<Term, Term> m_AnnotSSA;

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

	public AnnotateAndAssertCodeBlocks(SmtManager smtManager, NestedFormulas<Term, Term> nestedSSA, ILogger logger) {
		mLogger = logger;
		m_SmtManager = smtManager;
		m_Script = smtManager.getScript();
		m_Trace = nestedSSA.getTrace();
		m_SSA = nestedSSA;
	}

	protected Term annotateAndAssertPrecondition() {
		String name = precondAnnotation();
		Term annotated = annotateAndAssertTerm(m_SSA.getPrecondition(), name);
		return annotated;
	}

	protected String precondAnnotation() {
		return SSA + PRECOND;
	}

	protected Term annotateAndAssertPostcondition() {
		String name = postcondAnnotation();
		Term negatedPostcondition = m_Script.term("not", m_SSA.getPostcondition());
		Term annotated = annotateAndAssertTerm(negatedPostcondition, name);
		return annotated;
	}

	protected String postcondAnnotation() {
		return SSA + POSTCOND;
	}

	protected Term annotateAndAssertNonCall(int position) {
		String name;
		if (m_Trace.isReturnPosition(position)) {
			name = returnAnnotation(position);
		} else {
			name = internalAnnotation(position);
		}
		Term original = m_SSA.getFormulaFromNonCallPos(position);
		Term annotated = annotateAndAssertTerm(original, name);
		return annotated;
	}

	protected String internalAnnotation(int position) {
		return SSA + position;
	}

	protected String returnAnnotation(int position) {
		return SSA + position + RETURN;
	}

	protected Term annotateAndAssertLocalVarAssignemntCall(int position) {
		String name = localVarAssignemntCallAnnotation(position);
		Term indexed = m_SSA.getLocalVarAssignment(position);
		Term annotated = annotateAndAssertTerm(indexed, name);
		return annotated;
	}

	protected String localVarAssignemntCallAnnotation(int position) {
		return SSA + position + LOCVARASSIGN_CALL;
	}

	protected Term annotateAndAssertGlobalVarAssignemntCall(int position) {
		String name = globalVarAssignemntAnnotation(position);
		Term indexed = m_SSA.getGlobalVarAssignment(position);
		Term annotated = annotateAndAssertTerm(indexed, name);
		return annotated;
	}

	protected String globalVarAssignemntAnnotation(int position) {
		return SSA + position + GLOBVARASSIGN_CALL;
	}

	protected Term annotateAndAssertOldVarAssignemntCall(int position) {
		String name = oldVarAssignemntCallAnnotation(position);
		Term indexed = m_SSA.getOldVarAssignment(position);
		Term annotated = annotateAndAssertTerm(indexed, name);
		return annotated;
	}

	protected String oldVarAssignemntCallAnnotation(int position) {
		return SSA + position + OLDVARASSIGN_CALL;
	}

	protected Term annotateAndAssertPendingContext(int positionOfPendingContext, int pendingContextCode) {
		String name = pendingContextAnnotation(pendingContextCode);
		Term indexed = m_SSA.getPendingContext(positionOfPendingContext);
		Term annotated = annotateAndAssertTerm(indexed, name);
		return annotated;
	}

	protected String pendingContextAnnotation(int pendingContextCode) {
		return SSA + pendingContextCode + PENDINGCONTEXT;
	}

	protected Term annotateAndAssertLocalVarAssignemntPendingContext(int positionOfPendingReturn, int pendingContextCode) {
		String name = localVarAssignemntPendingReturnAnnotation(pendingContextCode);
		Term indexed = m_SSA.getLocalVarAssignment(positionOfPendingReturn);
		Term annotated = annotateAndAssertTerm(indexed, name);
		return annotated;
	}

	protected String localVarAssignemntPendingReturnAnnotation(int pendingContextCode) {
		return SSA + pendingContextCode + LOCVARASSIGN_PENDINGCONTEXT;
	}

	protected Term annotateAndAssertOldVarAssignemntPendingContext(int positionOfPendingReturn, int pendingContextCode) {
		String name = oldVarAssignemntPendingReturnAnnotation(pendingContextCode);
		Term indexed = m_SSA.getOldVarAssignment(positionOfPendingReturn);
		Term annotated = annotateAndAssertTerm(indexed, name);
		return annotated;
	}

	protected String oldVarAssignemntPendingReturnAnnotation(int pendingContextCode) {
		return SSA + pendingContextCode + OLDVARASSIGN_PENDINGCONTEXT;
	}

	protected Term annotateAndAssertTerm(Term term, String name) {
		assert term.getFreeVars().length == 0 : "Term has free vars";
		Annotation annot = new Annotation(":named", name);
		Term annotTerm = m_Script.annotate(term, annot);
		m_SmtManager.assertTerm(annotTerm);
		Term constantRepresentingAnnotatedTerm = m_Script.term(name);
		return constantRepresentingAnnotatedTerm;
	}
	
	
	/**
	 * Represents one conjunct in an annoted SSA.
	 * The annotated term is the term submitted to the solver (we have to
	 * use these named terms in order to obtain an unsatisfiable core).
	 *
	 */
	public static class AnnotatedSsaConjunct {
		private final Term m_AnnotedTerm;
		private final Term m_OriginalTerm;
		public AnnotatedSsaConjunct(Term annotedTerm, Term originalTerm) {
			super();
			m_AnnotedTerm = annotedTerm;
			m_OriginalTerm = originalTerm;
		}
		public Term getAnnotedTerm() {
			return m_AnnotedTerm;
		}
		public Term getOriginalTerm() {
			return m_OriginalTerm;
		}
		@Override
		public String toString() {
			return "AnnotatedSsaConjunct [m_AnnotedTerm=" + m_AnnotedTerm
					+ ", m_OriginalTerm=" + m_OriginalTerm + "]";
		}

	}
}
