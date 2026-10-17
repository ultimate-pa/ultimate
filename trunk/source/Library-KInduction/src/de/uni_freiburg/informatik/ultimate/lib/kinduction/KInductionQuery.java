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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem.StepVars;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem;

/**
 * The queries of k-induction on a {@link PcTransitionSystem}: the base and the step case for some {@code k},
 * strengthened by invariants at loop heads. {@link KInduction} asks them, and the probation of the invariant supplier
 * asks the very same ones on its own solver, to find out whether an invariant makes them slow.
 * <p>
 * Everything that declares a constant happens in {@link #prepare}, which has to be called before the {@code push} of a
 * query: constants declared inside a scope are forgotten by the solver on {@code pop}, but not by the constant cache.
 *
 * @param <STATE>
 *            the state type of the transition system's nodes
 * @author Max Barth (Max.Barth@lmu.de)
 */
public final class KInductionQuery<STATE> {

	/** The two queries of k-induction. */
	public enum Kind {
		/** Is {@code pc = FINAL} reachable from {@code pc = INIT} in {@code k} transitions? */
		BASE,
		/** Can {@code k} transitions from a non-INIT state without error reach an error? UNSAT: inductive. */
		STEP
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

	private final PcTransitionSystem<STATE> mSystem;
	private final ManagedScript mMgdScript;
	private final Object mLock;
	private final StepVars mConstants;
	private final List<Term> mStepTerms = new ArrayList<>();
	private final Map<TermVariable, IProgramVar> mVarOfTermVariable = new HashMap<>();

	/**
	 * @param lock
	 *            the owner of {@code mgdScript}'s lock, held by the caller while it asks queries
	 * @param constants
	 *            the constants of the unrolled steps, in {@code mgdScript}
	 */
	public KInductionQuery(final PcTransitionSystem<STATE> system, final ManagedScript mgdScript, final Object lock,
			final StepVars constants) {
		mSystem = system;
		mMgdScript = mgdScript;
		mLock = lock;
		mConstants = constants;
		for (final IProgramVar pv : system.getVars()) {
			mVarOfTermVariable.put(pv.getTermVariable(), pv);
		}
	}

	/**
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
	 * Declares everything the query for {@code k} needs: the steps up to {@code k}, the pc constants and the invariants.
	 * Must be called before the {@code push} of the query.
	 *
	 * @param invariants
	 *            pc node of a loop head -> its invariant
	 * @return the invariant assertions for the states {@code 0..k}
	 */
	public List<Term> prepare(final int k, final Map<Integer, Invariant> invariants) {
		while (mStepTerms.size() < k) {
			mStepTerms.add(mSystem.step(mStepTerms.size(), mConstants, mMgdScript));
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
				final Term atHead = SmtUtils.binaryEquality(script, mConstants.pc(j),
						PcTransitionSystem.pcValue(script, entry.getKey()));
				result.add(SmtUtils.implies(script, atHead, instantiated));
			}
		}
		return result;
	}

	/**
	 * Asserts the query of {@code kind} for {@code k}. Must be called inside the query's {@code push}, after
	 * {@link #prepare}.
	 *
	 * @param invariantAssertions
	 *            what {@link #prepare} returned for {@code k}
	 */
	public void assertQuery(final Kind kind, final int k, final List<Term> invariantAssertions) {
		final Script script = mMgdScript.getScript();
		final Term init = PcTransitionSystem.pcValue(script, PcTransitionSystem.INIT);
		final Term fin = PcTransitionSystem.pcValue(script, PcTransitionSystem.FINAL);
		if (kind == Kind.BASE) {
			mMgdScript.assertTerm(mLock, SmtUtils.binaryEquality(script, mConstants.pc(0), init));
		} else {
			mMgdScript.assertTerm(mLock, SmtUtils.distinct(script, mConstants.pc(0), init));
		}
		for (int j = 0; j < k; j++) {
			mMgdScript.assertTerm(mLock, mStepTerms.get(j));
		}
		if (kind == Kind.STEP) {
			for (int j = 0; j < k; j++) {
				mMgdScript.assertTerm(mLock, SmtUtils.distinct(script, mConstants.pc(j), fin));
			}
		}
		mMgdScript.assertTerm(mLock, SmtUtils.binaryEquality(script, mConstants.pc(k), fin));
		for (final Term invariant : invariantAssertions) {
			mMgdScript.assertTerm(mLock, invariant);
		}
	}
}
