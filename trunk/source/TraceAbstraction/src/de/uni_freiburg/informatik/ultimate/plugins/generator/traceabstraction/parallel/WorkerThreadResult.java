/*
 * Copyright (C) 2025 University of Freiburg
 * Copyright (C) 2025 LMU Munich
 * Copyright (C) 2025 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.NwaCegarLoop.AutomatonType;

public final class WorkerThreadResult<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>> {

	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mSubtrahend;
	private AutomatonType mAutomatonType;
	private ManagedScript mMgdScript;
	private IRun<L, ?> mCounterexample;
	PredicateFactory mPredicateFactory;
	private final boolean mWorkerCrashed;
	private final boolean mNoVerdict;
	private Map<IPredicate, Term> mProofInvariants;
	WorkerType mWorkerType;

	public enum WorkerType

	{
		TA, KINDUCTION, INVARIANT
	}

	/**
	 * The object returned by an @ICegarNwaWorkerThread
	 *
	 */
	public WorkerThreadResult(final WorkerType workerType,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend, final AutomatonType automatonType,
			final ManagedScript mgdScript, final IRun<L, ?> counterexample, final PredicateFactory predicateFactory,
			final boolean workerCrashed) {
		this(workerType, subtrahend, automatonType, mgdScript, counterexample, predicateFactory, workerCrashed, false);
	}

	private WorkerThreadResult(final WorkerType workerType,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend, final AutomatonType automatonType,
			final ManagedScript mgdScript, final IRun<L, ?> counterexample, final PredicateFactory predicateFactory,
			final boolean workerCrashed, final boolean noVerdict) {
		mWorkerType = workerType;
		mSubtrahend = subtrahend;
		mAutomatonType = automatonType;
		mMgdScript = mgdScript;
		mCounterexample = counterexample;
		mPredicateFactory = predicateFactory;
		mWorkerCrashed = workerCrashed;
		mNoVerdict = noVerdict;
	}

	/**
	 * A worker that ran to completion but neither proved nor refuted the program, for example because the solver
	 * answered {@code unknown}. It carries nothing to refine with, so the main thread can only retire the worker.
	 */
	public static <L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>> WorkerThreadResult<L, A>
			noVerdict(final WorkerType workerType) {
		return new WorkerThreadResult<>(workerType, null, null, null, null, null, false, true);
	}

	/**
	 * k-induction proved the whole program safe. Like every SAFE sentinel it has neither a subtrahend nor an automaton
	 * type.
	 *
	 * @param proofInvariants
	 *            for every loop head, a state of the initial abstraction, its invariant for a correctness witness,
	 *            terms of {@code mgdScript}; null if there are none
	 */
	public static <L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>> WorkerThreadResult<L, A>
			kInductionSafe(final Map<IPredicate, Term> proofInvariants, final ManagedScript mgdScript) {
		final WorkerThreadResult<L, A> result =
				new WorkerThreadResult<>(WorkerType.KINDUCTION, null, null, mgdScript, null, null, false, false);
		result.mProofInvariants = proofInvariants;
		return result;
	}

	/**
	 * @return for a k-induction proof the invariants for a correctness witness, see {@link #kInductionSafe}; null if
	 *         there are none
	 */
	public Map<IPredicate, Term> getProofInvariants() {
		return mProofInvariants;
	}

	public WorkerType getWorkerType() {
		return mWorkerType;
	}

	public boolean workerCrashed() {
		return mWorkerCrashed;
	}

	/**
	 * @return true if the worker finished without a verdict, see {@link #noVerdict(WorkerType)}.
	 */
	public boolean noVerdict() {
		return mNoVerdict;
	}

	public PredicateFactory getPredicateFactory() {
		return mPredicateFactory;
	}

	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getSubtrahend() {
		return mSubtrahend;
	}

	public AutomatonType getAutomatonType() {
		return mAutomatonType;
	}

	public ManagedScript getWorkerMgdScript() {
		return mMgdScript;
	}

	public IRun<L, ?> getCounterexample() {
		return mCounterexample;
	}

	public void garbageCollect() {
		mSubtrahend = null;
		mAutomatonType = null;
		mMgdScript = null;
		mCounterexample = null;
		mPredicateFactory = null;
	}
}