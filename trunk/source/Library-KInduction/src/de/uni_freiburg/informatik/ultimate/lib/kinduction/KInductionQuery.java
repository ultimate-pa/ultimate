/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
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
package de.uni_freiburg.informatik.ultimate.lib.kinduction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem.IStepVars;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * The queries of k-induction on a {@link PcTransitionSystem}: the base and the step case for some {@code k},
 * strengthened by invariants at loop heads. {@link KInduction} asks them, and the probation of the invariant supplier
 * asks the very same ones on its own solver, to find out whether an invariant makes them slow.
 * <p>
 * Everything that declares a constant happens in {@link #prepare}, which has to be called before the {@code push} of a
 * query: constants declared inside a scope are forgotten by the solver on {@code pop}, but not by the constant cache.
 * <p>
 * All steps but the last of a query occur in every query of a larger {@code k}, so they can stay in the solver: with
 * {@code keepStepsInSolver}, {@link #prepare} asserts them once, outside of any scope, each as an implication from a
 * guard, and a query asserts just the guards of its steps. The step terms are not kept here then. Whoever else uses the
 * solver does not assert the guards, so these steps do not constrain it.
 *
 * @author Max Barth (Max.Barth@lmu.de)
 * @param <STATE>
 *            the state type of the transition system's nodes
 */
public final class KInductionQuery<STATE> {

	private final PcTransitionSystem<STATE> mSystem;
	private final ManagedScript mMgdScript;
	private final Object mLock;
	private final IStepVars mConstants;
	private final boolean mKeepStepsInSolver;
	/**
	 * The first step of the base case for {@code k > 1}: the transitions from INIT into anything but FINAL.
	 */
	private final StepGroup mBaseCaseStart = new StepGroup("ki_guard_base_start");
	/**
	 * The first step of the step case for {@code k > 1}, which starts in a state that is not INIT.
	 */
	private final StepGroup mStepCaseStart = new StepGroup("ki_guard_step_start");
	/**
	 * Steps {@code 1, 2, ...} of both queries: the transitions neither from INIT nor into FINAL.
	 */
	private final StepGroup mMiddle = new StepGroup("ki_guard_middle");
	/**
	 * How many steps from neither INIT nor into FINAL there are, including that of {@link #mStepCaseStart}.
	 */
	private int mNumMiddleSteps;
	private boolean mBaseCaseStartBuilt;
	private long mLastMiddleStepDagSize;
	/**
	 * The transitions of a query's last step, from anywhere but INIT into FINAL, at {@link #mLastStepIndex}.
	 */
	private StepTerm mLastStep;
	private int mLastStepIndex = -1;
	/**
	 * The transitions from INIT into FINAL: the base case for {@code k = 1}.
	 */
	private StepTerm mOnlyStep;
	private long mAssertedDagSize;
	private final Map<TermVariable, IProgramVar> mVarOfTermVariable = new HashMap<>();

	/**
	 * Creates the queries over one transition system.
	 *
	 * @param system
	 *            the transition system to query
	 * @param mgdScript
	 *            the script all terms belong to
	 * @param lock
	 *            the owner of {@code mgdScript}'s lock, held by the caller while it asks queries
	 * @param constants
	 *            the constants of the unrolled steps, in {@code mgdScript}
	 * @param keepStepsInSolver
	 *            whether steps stay in the solver between queries, see the class javadoc. Then {@code k} must not
	 *            decrease from one query to the next, and {@link #solverRestarted} has to be called after a restart.
	 */
	public KInductionQuery(final PcTransitionSystem<STATE> system, final ManagedScript mgdScript, final Object lock,
			final IStepVars constants, final boolean keepStepsInSolver) {
		mSystem = system;
		mMgdScript = mgdScript;
		mLock = lock;
		mConstants = constants;
		mKeepStepsInSolver = keepStepsInSolver;
		for (final IProgramVar pv : system.getVars()) {
			mVarOfTermVariable.put(pv.getTermVariable(), pv);
		}
	}

	/**
	 * Returns the DAG size of the last step from the middle of a run built so far, 0 if there is none.
	 *
	 * @return the DAG size of the last step from the middle of a run built so far, 0 if there is none
	 */
	public long getLastStepDagSize() {
		return mLastMiddleStepDagSize;
	}

	/**
	 * Returns the DAG sizes of all step terms ever sent to the solver, counted each time one was sent.
	 *
	 * @return the DAG sizes of all step terms ever sent to the solver, counted each time one was sent
	 */
	public long getAssertedDagSize() {
		return mAssertedDagSize;
	}

	/**
	 * Returns the program variables of {@code invariant} with their term variables, or {@code null} if it mentions a
	 * variable that occurs in no transition of the system, which k-induction cannot use.
	 *
	 * @param invariant
	 *            the invariant to look at
	 * @return the program variables of {@code invariant} with their term variables, or {@code null} if it mentions a
	 *         variable that occurs in no transition of the system, which k-induction cannot use
	 */
	public Map<IProgramVar, TermVariable> variablesOf(final Term invariant) {
		final Map<IProgramVar, TermVariable> used = new LinkedHashMap<>();
		for (final TermVariable tv : invariant.getFreeVars()) {
			final IProgramVar pv = mVarOfTermVariable.get(tv);
			if (pv == null) {
				return null;
			}
			used.put(pv, tv);
		}
		return used;
	}

	/**
	 * Declares everything the query for {@code k} needs: the steps up to {@code k}, the pc constants and the
	 * invariants. Must be called before the {@code push} of the query.
	 *
	 * @param k
	 *            the number of unrolled steps
	 * @param invariants
	 *            pc node of a loop head -> its invariant
	 * @return the invariant assertions for the states {@code 0..k}
	 */
	public List<Term> prepare(final int k, final Map<Integer, Invariant> invariants) {
		while (mNumMiddleSteps < k - 1) {
			final StepTerm step = stepTerm(mNumMiddleSteps, false, false);
			mLastMiddleStepDagSize = step.dagSize();
			(mNumMiddleSteps == 0 ? mStepCaseStart : mMiddle).add(step);
			mNumMiddleSteps++;
		}
		if (mLastStepIndex != k - 1) {
			mLastStep = stepTerm(k - 1, false, true);
			mLastStepIndex = k - 1;
		}
		if (k == 1 && mOnlyStep == null) {
			mOnlyStep = stepTerm(0, true, true);
		}
		if (k > 1) {
			mOnlyStep = null;
			if (!mBaseCaseStartBuilt) {
				mBaseCaseStart.add(stepTerm(0, true, false));
				mBaseCaseStartBuilt = true;
			}
		}
		for (int j = 0; j <= k; j++) {
			mConstants.pc(j);
		}
		final List<Term> result = new ArrayList<>();
		final Script script = mMgdScript.getScript();
		for (final Map.Entry<Integer, Invariant> entry : invariants.entrySet()) {
			for (int j = 0; j <= k; j++) {
				final Map<Term, Term> substitution = new HashMap<>();
				for (final Map.Entry<IProgramVar, TermVariable> var : entry.getValue().vars().entrySet()) {
					substitution.put(var.getValue(), mConstants.var(var.getKey(), j));
				}
				final Term instantiated = PureSubstitution.apply(mMgdScript, substitution, entry.getValue().term());
				final Term atHead =
						SmtUtils.binaryEquality(script, mConstants.pc(j), mSystem.pcValue(script, entry.getKey()));
				result.add(SmtUtils.implies(script, atHead, instantiated));
			}
		}
		return result;
	}

	private StepTerm stepTerm(final int idx, final boolean fromInit, final boolean intoFinal) {
		final Term term = mSystem.step(idx, mConstants, mMgdScript, fromInit, intoFinal);
		return new StepTerm(term, PcTransitionSystem.dagSize(term));
	}

	/**
	 * The solver was restarted with the declarations and the stack it had but no assertions, so the next
	 * {@link #prepare} has to send the steps again. The guards were declared and stay.
	 */
	public void solverRestarted() {
		mNumMiddleSteps = 0;
		mBaseCaseStartBuilt = false;
	}

	/**
	 * Asserts the query of {@code kind} for {@code k}. Must be called inside the query's {@code push}, after
	 * {@link #prepare}.
	 * <p>
	 * Both queries ask for a run that reaches FINAL exactly at its end, so each step holds only the transitions that
	 * can be taken at its place. That FINAL is not reached earlier, and that the step case does not start in INIT, is
	 * therefore implied. Nothing is lost by the base case not looking for an earlier error: the queries of smaller
	 * {@code k} have ruled that out already.
	 *
	 * @param kind
	 *            the kind of the query
	 * @param k
	 *            the number of unrolled steps
	 * @param invariantAssertions
	 *            what {@link #prepare} returned for {@code k}
	 */
	public void assertQuery(final Kind kind, final int k, final List<Term> invariantAssertions) {
		assert !mKeepStepsInSolver || mNumMiddleSteps == k - 1 : "k must not decrease with the steps in the solver";
		final Script script = mMgdScript.getScript();
		final Term init = mSystem.pcValue(script, PcTransitionSystem.INIT);
		final Term fin = mSystem.pcValue(script, PcTransitionSystem.FINAL);
		if (kind == Kind.BASE) {
			mMgdScript.assertTerm(mLock, SmtUtils.binaryEquality(script, mConstants.pc(0), init));
		}
		if (kind == Kind.BASE && k == 1) {
			assertStep(mOnlyStep);
		} else {
			if (k > 1) {
				(kind == Kind.BASE ? mBaseCaseStart : mStepCaseStart).assertSteps(1);
				mMiddle.assertSteps(k - 2);
			}
			assertStep(mLastStep);
		}
		mMgdScript.assertTerm(mLock, SmtUtils.binaryEquality(script, mConstants.pc(k), fin));
		for (final Term invariant : invariantAssertions) {
			mMgdScript.assertTerm(mLock, invariant);
		}
	}

	private void assertStep(final StepTerm step) {
		mMgdScript.assertTerm(mLock, step.term());
		mAssertedDagSize += step.dagSize();
	}

	/** The two queries of k-induction. */
	public enum Kind {
		/**
		 * Is {@code pc = FINAL} reached first after exactly {@code k} transitions from {@code pc = INIT}? Asked for
		 * {@code k = 1, 2, ...}, this finds every error within {@code k}.
		 */
		BASE,
		/**
		 * Can {@code k} transitions from a non-INIT state without error reach an error? UNSAT: inductive.
		 */
		STEP
	}

	/**
	 * A step term as it is sent to the solver, with its DAG size.
	 *
	 * @param term
	 *            the step term
	 * @param dagSize
	 *            the number of nodes of the DAG of {@code term}
	 */
	private record StepTerm(Term term, long dagSize) {
	}

	/**
	 * An invariant of a loop head, with the program variables it mentions.
	 *
	 * @param term
	 *            a state predicate over the program variables' term variables
	 * @param vars
	 *            the program variables of {@code term}, with their term variables
	 */
	public record Invariant(Term term, Map<IProgramVar, TermVariable> vars) {
	}

	/** Steps that the same queries use: behind one guard in the solver, or here until a query asserts them. */
	private final class StepGroup {
		private final String mGuardName;
		private final List<StepTerm> mSteps = new ArrayList<>();
		private Term mGuard;

		private StepGroup(final String guardName) {
			mGuardName = guardName;
		}

		private void add(final StepTerm step) {
			if (!mKeepStepsInSolver) {
				mSteps.add(step);
				return;
			}
			if (mGuard == null) {
				mMgdScript.declareFun(mLock, mGuardName, new Sort[0], SmtSortUtils.getBoolSort(mMgdScript));
				mGuard = mMgdScript.getScript().term(mGuardName);
			}
			// Not SmtUtils.implies, which would flatten the DAG of the step.
			mMgdScript.assertTerm(mLock, mMgdScript.getScript().term("=>", mGuard, step.term()));
			mAssertedDagSize += step.dagSize();
		}

		/**
		 * Asserts the first {@code count} steps of this group. With the steps in the solver, that means all of them.
		 */
		private void assertSteps(final int count) {
			if (mKeepStepsInSolver) {
				if (mGuard != null) {
					mMgdScript.assertTerm(mLock, mGuard);
				}
				return;
			}
			for (final StepTerm step : mSteps.subList(0, count)) {
				assertStep(step);
			}
		}
	}
}
