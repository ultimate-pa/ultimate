/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.PrePostConditionSpecification;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Performs validity checks of {@link IFloydHoareAnnotation}s.
 *
 * This is an abstract base class which must be specialized depending on what is annotated, e.g. for nested word
 * automata (see {@link NwaFloydHoareValidityCheck}) or interprocedural control flow graphs (see
 * {@link IcfgFloydHoareValidityCheck}).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            The type of states which are annotated
 */
public abstract class FloydHoareValidityCheck<S> {
	protected final ILogger mLogger;
	private final MonolithicImplicationChecker mImplChecker;
	private final IHoareTripleChecker mHoareTripleChecker;

	private final IFloydHoareAnnotation<S> mAnnotation;
	private final PrePostConditionSpecification<S> mSpec;

	private final boolean mAssertValidity;
	private final MissingAnnotationBehaviour mMissingAnnotations;
	private final boolean mCheckSafety;

	private int mProven;
	private int mRefuted;
	private int mUnknown;
	private int mMissing;

	private final ArrayDeque<S> mWorklist = new ArrayDeque<>();
	private final Set<S> mVisited = new HashSet<>();

	private Validity mIsInitial;
	private Validity mIsInductive;
	private Validity mIsSafe = Validity.VALID;

	/**
	 * Specifies how to proceed for states that do not have an annotation.
	 */
	public enum MissingAnnotationBehaviour {
		IGNORE, THROW, UNKNOWN
	}

	private interface ISimpleHoareCheck<A extends IAction> {
		Validity check(IPredicate pre, A action, IPredicate post);
	}

	protected FloydHoareValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IHoareTripleChecker hoareTripleChecker, final IFloydHoareAnnotation<S> annotation,
			final boolean assertValidity, final MissingAnnotationBehaviour missingAnnotations,
			final boolean checkSafety) {
		mLogger = services.getLoggingService().getLogger(FloydHoareValidityCheck.class);
		mImplChecker = new MonolithicImplicationChecker(services, mgdScript);
		mHoareTripleChecker = hoareTripleChecker;

		mAnnotation = annotation;
		mSpec = mAnnotation.getSpecification();

		mAssertValidity = assertValidity;
		mMissingAnnotations = missingAnnotations;
		mCheckSafety = checkSafety;
		if (!mCheckSafety) {
			mIsSafe = Validity.NOT_CHECKED;
		}
	}

	protected final void performCheck() {
		mIsInitial = checkInitial();
		mIsInductive = checkInductivity();
		// NOTE: checkInductivity() also determines mIsSafe
	}

	public Validity isInitial() {
		return mIsInitial;
	}

	public Validity isInductive() {
		return mIsInductive;
	}

	public Validity isSafe() {
		return mIsSafe;
	}

	public Validity isValid() {
		if (mCheckSafety) {
			return mIsInitial.and(mIsInductive).and(mIsSafe);
		}
		return mIsInitial.and(mIsInductive);
	}

	public boolean getResult() {
		return isValid() != Validity.INVALID;
	}

	protected abstract Iterable<Pair<IInternalAction, S>> getInternalSuccessors(S state);

	protected abstract Iterable<Pair<ICallAction, S>> getCallSuccessors(S state);

	protected abstract Iterable<Triple<IReturnAction, S, S>> getReturnSuccessors(S state);

	private Validity checkInitial() {
		Validity result = Validity.VALID;
		for (final var initial : mSpec.getInitialStates()) {
			// check initial states are labeled with precondition (or weaker)
			final IPredicate pred = getAnnotation(initial);
			if (pred != null) {
				final var precondition = mSpec.getPrecondition(initial);
				final var check = mImplChecker.checkImplication(precondition, false, pred, false);
				assert !mAssertValidity || check != Validity.INVALID : "condition " + pred + " at initial location "
						+ initial + " not entailed by corresponding precondition " + precondition;
				result = result.and(check);
			}

			// initialize data structures for DFS performed by inductivity check
			mWorklist.add(initial);
			mVisited.add(initial);
		}

		return result;
	}

	private Validity checkInductivity() {
		Validity result = Validity.VALID;
		while (!mWorklist.isEmpty()) {
			final S state = mWorklist.pop();
			final IPredicate pre = getAnnotation(state);
			checkSafe(state, pre);

			for (final var outTrans : getInternalSuccessors(state)) {
				final Validity inductivity = checkInductivity(state, pre, outTrans, mHoareTripleChecker::checkInternal);
				result = result.and(inductivity);
			}
			for (final var outTrans : getCallSuccessors(state)) {
				final Validity inductivity = checkInductivity(state, pre, outTrans, mHoareTripleChecker::checkCall);
				result = result.and(inductivity);
			}
			for (final var outTrans : getReturnSuccessors(state)) {
				final Validity inductivity = checkReturnInductivity(state, pre, outTrans);
				result = result.and(inductivity);
			}
		}
		if (mHoareTripleChecker instanceof IncrementalHoareTripleChecker) {
			((IncrementalHoareTripleChecker) mHoareTripleChecker).clearAssertionStack();
		}
		mLogger.info(
				"Floyd-Hoare annotation has %d edges. %d inductive. %d not inductive. "
						+ "%d times theorem prover too weak to decide inductivity. %d times interpolants missing.",
				mProven + mRefuted + mUnknown + mMissing, mProven, mRefuted, mUnknown, mMissing);
		return result;
	}

	private <A extends IAction> Validity checkInductivity(final S state, final IPredicate pre,
			final Pair<A, S> transition, final ISimpleHoareCheck<A> checker) {
		final var succ = transition.getSecond();
		if (mVisited.add(succ)) {
			mWorklist.push(succ);
		}

		final IPredicate post = getAnnotation(succ);
		if (pre == null || post == null) {
			mMissing++;
			return mMissingAnnotations == MissingAnnotationBehaviour.IGNORE ? Validity.VALID : Validity.UNKNOWN;
		}

		final Validity inductivity = checker.check(pre, transition.getFirst(), post);
		evaluateInductivityResult(inductivity, state, transition.getFirst(), succ, null);
		return inductivity;
	}

	private Validity checkReturnInductivity(final S state, final IPredicate pre,
			final Triple<IReturnAction, S, S> transition) {
		final var succ = transition.getSecond();
		if (mVisited.add(succ)) {
			mWorklist.push(succ);
		}

		final IPredicate post = getAnnotation(succ);
		final IPredicate hier = getAnnotation(transition.getThird());
		if (pre == null || post == null || hier == null) {
			mMissing++;
			return mMissingAnnotations == MissingAnnotationBehaviour.IGNORE ? Validity.VALID : Validity.UNKNOWN;
		}

		final Validity inductivity = mHoareTripleChecker.checkReturn(pre, hier, transition.getFirst(), post);
		evaluateInductivityResult(inductivity, state, transition.getFirst(), succ, transition.getThird());
		return inductivity;
	}

	private void evaluateInductivityResult(final Validity inductivity, final S state, final IAction trans, final S succ,
			final S hier) {
		switch (inductivity) {
		case VALID:
			mProven++;
			break;
		case INVALID:
			mRefuted++;
			final String hierString = hier == null ? "" : (" (hier: " + hier + ")");
			mLogger.warn("Transition %s %s %s%s not inductive", state, trans, succ, hierString);
			assert !mAssertValidity : "inductivity violated";
			break;
		case UNKNOWN:
			mUnknown++;
			break;
		default:
			throw new IllegalArgumentException("unexpected validity: " + inductivity);
		}
	}

	private void checkSafe(final S state, final IPredicate pred) {
		if (!mCheckSafety) {
			return;
		}

		if (pred == null && mMissingAnnotations == MissingAnnotationBehaviour.UNKNOWN) {
			mIsSafe = mIsSafe.and(Validity.UNKNOWN);
			return;
		}

		if (pred == null || !mSpec.isFinalState(state)) {
			return;
		}

		final var check = mImplChecker.checkImplication(pred, false, mSpec.getPostcondition(), false);
		assert !mAssertValidity || check != Validity.INVALID : "post condition " + mSpec.getPostcondition()
				+ "not entailed by condition " + pred + " at state " + state;
		mIsSafe = mIsSafe.and(check);
	}

	private IPredicate getAnnotation(final S state) {
		final var predicate = mAnnotation.getAnnotation(state);
		if (predicate == null) {
			mLogger.warn("%s has no Hoare annotation", state);
			if (mMissingAnnotations == MissingAnnotationBehaviour.THROW) {
				throw new IllegalArgumentException(state + " has no Hoare annotation");
			}
		}
		return predicate;
	}
}
