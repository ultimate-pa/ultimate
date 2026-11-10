/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE KInduction Library.
 *
 * The ULTIMATE KInduction Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE KInduction Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE KInduction Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE KInduction Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE KInduction Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallNode;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.ProcedureSummaries;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

/**
 * The letters a violation witness can name, read off the chains of cut-graph states that the model of a satisfiable base
 * case takes, see {@link PcTransitionSystem#getChainOfStep}. They are a <em>subsequence</em> of the letters of the
 * violation: this is neither a nested word nor a run of the abstraction, and consecutive letters need not be connected.
 * <p>
 * A witness stands for all executions that pass its waypoints, so that a waypoint may be left out, but a follow waypoint
 * has to be passed whenever it is evaluated. A location therefore has a waypoint either at <b>every</b> visit or at
 * none. Hence the rules for two consecutive states {@code u, v} of a chain:
 * <ul>
 * <li>If exactly one internal letter leads from {@code u} to {@code v}, and the edge in the graph stands for nothing
 * else, this letter was taken, and it is kept.
 * <li>Otherwise it is not known what happened at {@code u}, and <b>no</b> visit of {@code u} keeps its letter: several
 * letters were united to one edge, or a chain through states that {@link ProcedureSummaries} removed was united with
 * the letter, or this is a call, a return or a summarized call.
 * </ul>
 * What a gap hides cannot clash with a letter that is kept: {@link ProcedureSummaries} summarizes a procedure at all of
 * its call sites or at none, and it removes a state for good, so their letters are never kept. Call and return letters
 * are always left out. Without values, a {@code function_return} waypoint would say nothing, and leaving out all of them
 * cannot leave a call without its return.
 * <p>
 * The last letter leads to the error state of the violation, which is the target of the witness. In a program with a
 * {@code CallStack} a node does not say which activation it belongs to, so there the target is the only letter.
 * <p>
 * The model alone proves the violation. If the letters cannot be named as above, fewer are, see {@link Level}.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class KInductionWaypoints<LETTER extends IAction, STATE> {

	/**
	 * How much of the violation the waypoint letters name. The violation is proved by the model alone, so a witness that
	 * cannot be built in full is built with less, never not at all.
	 */
	public enum Level {
		/** The letters as the rules above give them. */
		FULL,
		/** Only the target: a chain could not be read or its letters not be named, so no other letter is known to be safe. */
		TARGET_ONLY,
		/** No letter: the target is not known. The violation is reported at {@link #getErrorState()} without a waypoint. */
		EMPTY
	}

	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	private final Map<STATE, Set<STATE>> mComposedEdges;
	private final List<LETTER> mLetters;
	private final LETTER mTarget;
	private final STATE mErrorState;
	private final boolean mErrorStateGuessed;
	private final Level mLevel;
	private final RuntimeException mDegradeCause;
	private int mNumSuppressedStates;

	/**
	 * @param chains
	 *            the chain of every step of the violation, in order, null for a step whose chain could not be read; null
	 *            if no chain could be read. The last state of the last one is the error state.
	 * @param chainFailure
	 *            why a chain could not be read, null if all could
	 * @param composedEdges
	 *            see {@link ProcedureSummaries#getComposedEdges()}
	 * @param onlyTarget
	 *            whether only the letter into the error state is to be kept
	 * @throws KInductionCounterexampleException
	 *             if the abstraction has no error state at all
	 */
	KInductionWaypoints(final INestedWordAutomaton<LETTER, STATE> abstraction, final List<List<CallNode<STATE>>> chains,
			final RuntimeException chainFailure, final Map<STATE, Set<STATE>> composedEdges, final boolean onlyTarget) {
		mAbstraction = abstraction;
		mComposedEdges = composedEdges;

		RuntimeException cause = chainFailure;
		final List<CallNode<STATE>> lastChain = chains == null ? null : lastNonEmpty(chains);
		CallNode<STATE> error = null;
		LETTER target = null;
		if (lastChain == null) {
			if (cause == null) {
				cause = new KInductionCounterexampleException("k-induction refuted the program, but the model has no "
						+ "chain");
			}
		} else {
			error = lastChain.get(lastChain.size() - 1);
			try {
				target = targetLetter(lastChain, error);
			} catch (final KInductionCounterexampleException e) {
				cause = e;
			}
		}
		if (error != null && mAbstraction.isFinal(error.getState())) {
			mErrorState = error.getState();
			mErrorStateGuessed = false;
		} else {
			mErrorState = someErrorState();
			mErrorStateGuessed = true;
		}
		mTarget = target;

		final List<LETTER> letters = new ArrayList<>();
		Level level = Level.FULL;
		if (target == null) {
			level = Level.EMPTY;
		} else if (chainFailure != null) {
			level = Level.TARGET_ONLY;
		} else if (!onlyTarget) {
			try {
				letters.addAll(namedLetters(chains, error));
			} catch (final RuntimeException e) {
				letters.clear();
				level = Level.TARGET_ONLY;
				cause = e;
			}
		}
		if (target != null) {
			letters.add(target);
		}
		mLevel = level;
		mDegradeCause = level == Level.FULL ? null : cause;
		mLetters = Collections.unmodifiableList(letters);
	}

	/** The letters of the rules above, but the target. */
	private List<LETTER> namedLetters(final List<List<CallNode<STATE>>> chains, final CallNode<STATE> error) {
		final Set<STATE> suppressed = new HashSet<>();
		final List<StateAndLetter<LETTER, STATE>> named = new ArrayList<>();
		for (final List<CallNode<STATE>> chain : chains) {
			for (int i = 0; i + 1 < chain.size(); i++) {
				final CallNode<STATE> from = chain.get(i);
				final CallNode<STATE> to = chain.get(i + 1);
				final LETTER letter = uniqueLetter(from, to);
				if (letter == null) {
					suppressed.add(from.getState());
				} else if (!to.equals(error)) {
					named.add(new StateAndLetter<>(from.getState(), letter));
				}
			}
		}
		final List<LETTER> letters = new ArrayList<>();
		for (final StateAndLetter<LETTER, STATE> entry : named) {
			if (!suppressed.contains(entry.state())) {
				letters.add(entry.letter());
			}
		}
		mNumSuppressedStates = suppressed.size();
		return letters;
	}

	/** Any error state, for a violation whose model does not say which one it reaches. */
	private STATE someErrorState() {
		for (final STATE state : mAbstraction.getFinalStates()) {
			return state;
		}
		throw new KInductionCounterexampleException("k-induction refuted the program, but its abstraction has no error "
				+ "state");
	}

	private record StateAndLetter<LETTER, STATE>(STATE state, LETTER letter) {
	}

	/**
	 * @return the chain of the last step that has states, or null if there is none or if a step after it, or it, could
	 *         not be read, since that might have been the step into the error
	 */
	private static <STATE> List<CallNode<STATE>> lastNonEmpty(final List<List<CallNode<STATE>>> chains) {
		for (int i = chains.size() - 1; i >= 0; i--) {
			final List<CallNode<STATE>> chain = chains.get(i);
			if (chain == null) {
				return null;
			}
			if (!chain.isEmpty()) {
				return chain;
			}
		}
		return null;
	}

	/** @return the only letter the step from {@code from} to {@code to} can have taken, or null if it is not known */
	private LETTER uniqueLetter(final CallNode<STATE> from, final CallNode<STATE> to) {
		final STATE source = from.getState();
		if (!from.sibling(to.getState()).equals(to)
				|| mComposedEdges.getOrDefault(source, Collections.emptySet()).contains(to.getState())) {
			return null;
		}
		LETTER result = null;
		for (final OutgoingInternalTransition<LETTER, STATE> out : mAbstraction.internalSuccessors(source)) {
			if (out.getSucc().equals(to.getState())) {
				if (result != null) {
					return null;
				}
				result = out.getLetter();
			}
		}
		return result;
	}

	/**
	 * The letter that names the error: the one the last step took, or, if that is not known (an error inside a summarized
	 * callee, say), any letter into the error state, as long as all of them have the same location.
	 */
	private LETTER targetLetter(final List<CallNode<STATE>> lastChain, final CallNode<STATE> error) {
		if (!mAbstraction.isFinal(error.getState())) {
			throw new KInductionCounterexampleException(
					"k-induction refuted the program, but the model's last chain ends in " + error
							+ ", which is no error state");
		}
		if (lastChain.size() > 1) {
			final LETTER unique = uniqueLetter(lastChain.get(lastChain.size() - 2), error);
			if (unique != null) {
				return unique;
			}
		}
		final Set<String> locations = new LinkedHashSet<>();
		LETTER result = null;
		for (final IncomingInternalTransition<LETTER, STATE> in : mAbstraction.internalPredecessors(error.getState())) {
			result = in.getLetter();
			locations.add(locationOf(result));
		}
		if (result == null) {
			throw new KInductionCounterexampleException(
					"k-induction refuted the program, but no internal letter leads to the error state " + error);
		}
		if (locations.size() != 1) {
			throw new KInductionCounterexampleException("k-induction refuted the program, but the letters into the error "
					+ "state " + error + " have the locations " + locations + ", so a target cannot be named");
		}
		return result;
	}

	private String locationOf(final LETTER letter) {
		if (!(letter instanceof IElement)) {
			throw new KInductionCounterexampleException("the letter " + letter + " has no location");
		}
		final ILocation location = ILocation.getAnnotation((IElement) letter);
		if (location == null) {
			throw new KInductionCounterexampleException("the letter " + letter + " has no location");
		}
		return location.getFileName() + ":" + location.getStartLine() + ":" + location.getStartColumn();
	}

	/**
	 * The letters, in the order of the violation. The last one leads to the error state; empty at {@link Level#EMPTY}.
	 */
	public List<LETTER> getLetters() {
		return mLetters;
	}

	/** @return the letter into the error state, null at {@link Level#EMPTY} */
	public LETTER getTargetLetter() {
		return mTarget;
	}

	/** @return the error state of the violation, see {@link #isErrorStateGuessed()} */
	public STATE getErrorState() {
		return mErrorState;
	}

	/**
	 * @return true if the model did not say which error state it reaches, so that {@link #getErrorState()} is just one
	 *         of them: the program is incorrect, but maybe at another error state
	 */
	public boolean isErrorStateGuessed() {
		return mErrorStateGuessed;
	}

	public Level getLevel() {
		return mLevel;
	}

	/** @return why the level is below {@link Level#FULL}, null at {@link Level#FULL} */
	public RuntimeException getDegradeCause() {
		return mDegradeCause;
	}

	/** How many states of the abstraction no letter was kept for, although a chain passes them. */
	public int getNumSuppressedStates() {
		return mNumSuppressedStates;
	}
}
