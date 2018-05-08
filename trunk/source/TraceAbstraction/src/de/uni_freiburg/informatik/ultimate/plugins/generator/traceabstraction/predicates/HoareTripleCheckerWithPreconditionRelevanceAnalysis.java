/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Allows several preconditions. Tries to detect which of them are relevant
 * to prove the implication.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class HoareTripleCheckerWithPreconditionRelevanceAnalysis extends IncrementalHoareTripleChecker {
		
		private List<IPredicate> mAssertedPrecond;

		public HoareTripleCheckerWithPreconditionRelevanceAnalysis(final CfgSmtToolkit csToolkit) {
			super(csToolkit, false);
		}
		
		
		private LBool assertPrecondition(final List<IPredicate> pres) {
			assert mManagedScript.isLockOwner(this);
			assert mAssertedAction != null : "Assert CodeBlock first";
			assert mAssertedPrecond == null : "precond already asserted";
			mAssertedPrecond = pres;
			mEdgeCheckerBenchmark.continueEdgeCheckerTime();
			mManagedScript.push(this, 1);
			LBool quickCheck = null;
			
			final Set<IProgramVar> vars = new HashSet<>();
			for (int i=0; i<pres.size(); i++) {
				Term predcondition = pres.get(i).getClosedFormula();
				if (mUseNamedTerms) {
					final Annotation annot = new Annotation(":named", getIdentifierForPrecond(i));
					predcondition = mManagedScript.annotate(this, predcondition, annot);
				}
				quickCheck = mManagedScript.assertTerm(this, predcondition);
				vars.addAll(pres.get(i).getVars());
			}
			final String predProc = mAssertedAction.getPrecedingProcedure();
			final Set<IProgramNonOldVar> modifiableGlobals = mModifiableGlobalVariableManager.getModifiedBoogieVars(predProc);
			
		final Collection<Term> oldVarEqualities = constructNonModOldVarsEquality(vars, modifiableGlobals,
				mManagedScript, this);
			if (!oldVarEqualities.isEmpty()) {
				Term nonModOldVarsEquality = SmtUtils.and(mManagedScript.getScript(), oldVarEqualities.toArray(new Term[oldVarEqualities.size()]));
				if (mUseNamedTerms) {
					final Annotation annot = new Annotation(":named", ID_PRECONDITION_NON_MOD_GLOBAL_EQUALITY);
					nonModOldVarsEquality = mManagedScript.annotate(this, nonModOldVarsEquality, annot);
				}
				quickCheck = mManagedScript.assertTerm(this, nonModOldVarsEquality);
			}
			mEdgeCheckerBenchmark.stopEdgeCheckerTime();
			return quickCheck;
		}


		private String getIdentifierForPrecond(final int i) {
			return ID_PRECONDITION + i;
		}
		
		private void unAssertPrecondition() {
			assert mManagedScript.isLockOwner(this);
			assert mAssertedPrecond != null : "No PrePred asserted";
			mAssertedPrecond = null;
			mManagedScript.pop(this, 1);

			if (mAssertedAction == null) {
				throw new AssertionError("CodeBlock is assigned first");
			}
		}
		
		
		
		public Pair<Validity, List<IPredicate>> checkInternal(
				final List<IPredicate> pre, final IInternalAction act, final IPredicate post) {
			assertCodeBlock(act);
			assertPrecondition(pre);
			assertPostcond(post);
			final Validity validity = checkValidity();
			final List<IPredicate> preconditionsInUnsatCore;
			if (validity == Validity.VALID) {
				preconditionsInUnsatCore = determinePreconditionsInUnsatCore();
			} else {
				preconditionsInUnsatCore = null;
			}
			unAssertPostcondition();
			unAssertPrecondition();
			unAssertCodeBlock();
			return new Pair<Validity, List<IPredicate>>(validity, preconditionsInUnsatCore);
		}
		



		private List<IPredicate> determinePreconditionsInUnsatCore() {
			final Term[] unsatCore = mManagedScript.getUnsatCore(this);
			final Set<String> idsInUnsatCore = new HashSet<>();
			for (final Term term : unsatCore) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				idsInUnsatCore.add(appTerm.getFunction().getApplicationString());
			}
			final List<IPredicate> result = new ArrayList<>();
			for (int i=0; i<mAssertedPrecond.size(); i++) {
				if (idsInUnsatCore.contains(getIdentifierForPrecond(i))) {
					result.add(mAssertedPrecond.get(i));
				} 
			}
			return result;
		}


		public Pair<Validity, List<IPredicate>> checkCall(final List<IPredicate> pre, final ICallAction act, final IPredicate post) {
			assertCodeBlock(act);
			assertPrecondition(pre);
			assertPostcond(post);
			final Validity validity = checkValidity();
			final List<IPredicate> preconditionsInUnsatCore;
			if (validity == Validity.VALID) {
				preconditionsInUnsatCore = determinePreconditionsInUnsatCore();
			} else {
				preconditionsInUnsatCore = null;
			}
			unAssertPostcondition();
			unAssertPrecondition();
			unAssertCodeBlock();
			return new Pair<Validity, List<IPredicate>>(validity, preconditionsInUnsatCore);
		}
		
		public Pair<Validity, List<IPredicate>> checkReturn(final List<IPredicate> linPre, final IPredicate hierPre,
				final IReturnAction act, final IPredicate post) {
			assertCodeBlock(act);
			assertPrecondition(linPre);
			assertHierPred(hierPre);
			assertPostcond(post);
			final Validity validity = checkValidity();
			final List<IPredicate> preconditionsInUnsatCore;
			if (validity == Validity.VALID) {
				preconditionsInUnsatCore = determinePreconditionsInUnsatCore();
			} else {
				preconditionsInUnsatCore = null;
			}
			unAssertPostcondition();
			unAssertHierPred();
			unAssertPrecondition();
			unAssertCodeBlock();
			return new Pair<Validity, List<IPredicate>>(validity, preconditionsInUnsatCore);
		}
		
	}