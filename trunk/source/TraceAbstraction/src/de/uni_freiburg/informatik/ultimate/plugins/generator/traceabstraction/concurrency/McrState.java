/*
 * Copyright (C) 2021-2022 Dennis Wölfing
 * Copyright (C) 2021-2022 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgForkThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgJoinThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.LeftRightSplit.Direction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * All the information for MCR to be encoded in automaton states.
 *
 * @author Dennis Wölfing
 *
 * @param <L>
 *            The letters of the automaton.
 * @param <S>
 *            The type of states in the input automaton.
 */
public class McrState<L extends IIcfgTransition<?>> implements IMcrState<L> {
	private static final boolean OPTIMIZE_DEAD_ENDS = true;

	private final IMLPredicate mOldState;
	private final Map<String, DependencyRank> mThreads;
	private final Map<IProgramVar, DependencyRank> mVariables;
	private final Map<IProgramVar, L> mLastWriteSt;
	private final L mLastStatement;
	private final Set<LeftRightSplit<L>> mLeftRightSplits;

	/**
	 * Constructs a new McrState for the initial state.
	 *
	 * @param state
	 *            The initial state in the input automaton.
	 */
	public McrState(final IMLPredicate state) {
		mOldState = state;
		mThreads = Collections.emptyMap();
		mVariables = Collections.emptyMap();
		mLastWriteSt = Collections.emptyMap();
		mLastStatement = null;
		mLeftRightSplits = Collections.emptySet();
	}

	/**
	 * Constructs a new McrState.
	 *
	 * @param oldState
	 *            The state in the input automaton.
	 * @param threads
	 *            The dependency rank of the last statements executed in each thread.
	 * @param variables
	 *            The dependency rank of the last write for each variable.
	 * @param lastWriteSt
	 *            The last write statement for each variable.
	 * @param lastStatement
	 *            The last statement executed.
	 * @param leftRightSplits
	 *            The set of left-right splits.
	 */
	public McrState(final IMLPredicate oldState, final Map<String, DependencyRank> threads,
			final Map<IProgramVar, DependencyRank> variables, final Map<IProgramVar, L> lastWriteSt,
			final L lastStatement, final Set<LeftRightSplit<L>> leftRightSplits) {
		mOldState = oldState;
		mThreads = threads;
		mVariables = variables;
		mLastWriteSt = lastWriteSt;
		mLastStatement = lastStatement;
		mLeftRightSplits = leftRightSplits;
	}

	@Override
	public IMLPredicate getOldState() {
		return mOldState;
	}

	private static <L extends IIcfgTransition<?>> Set<String> getThreadId(final L transition) {
		if (transition instanceof IcfgForkThreadOtherTransition) {
			return Set.of(transition.getPrecedingProcedure(), transition.getSucceedingProcedure());
		}
		if (transition instanceof IcfgJoinThreadOtherTransition) {
			return Set.of(transition.getPrecedingProcedure(), transition.getSucceedingProcedure());
		}

		assert transition.getPrecedingProcedure().equals(transition.getSucceedingProcedure());
		return Set.of(transition.getPrecedingProcedure());
	}

	/**
	 * Calculate the McrState after executing the given statement.
	 *
	 * @param transition
	 *            The transition to take.
	 * @param successor
	 *            The state of the input automaton after executing the statement.
	 * @return The new McrState.
	 */
	@Override
	public McrState<L> getNextState(final L transition, final IMLPredicate successor) {
		final UnmodifiableTransFormula tf = transition.getTransformula();
		final Set<IProgramVar> reads = tf.getInVars().keySet();
		final Set<IProgramVar> writes = tf.getOutVars().keySet();

		DependencyRank deprank = new DependencyRank();
		for (final String thread : getThreadId(transition)) {
			if (mThreads.containsKey(thread)) {
				deprank = deprank.getMax(mThreads.get(thread));
			}
		}

		for (final IProgramVar var : reads) {
			final DependencyRank varRank = mVariables.get(var);
			deprank = deprank.getMax(varRank);
		}

		// TODO: hashCode is not good rank.
		final int rank = transition.hashCode();
		deprank = deprank.add(rank);

		DependencyRank lastStDeprank;
		if (mLastStatement != null) {
			lastStDeprank = mThreads.get(getThreadId(mLastStatement).iterator().next());
			assert lastStDeprank != null;
		} else {
			lastStDeprank = null;
		}

		boolean dependentOnLast = mLastStatement == null
				|| DataStructureUtils.haveNonEmptyIntersection(getThreadId(transition), getThreadId(mLastStatement))
				|| DataStructureUtils.haveNonEmptyIntersection(reads,
						mLastStatement.getTransformula().getOutVars().keySet());

		final Set<LeftRightSplit<L>> newLeftRightSplits = new HashSet<>();

		for (final LeftRightSplit<L> split : mLeftRightSplits) {
			final LeftRightSplit<L> newSplit = new LeftRightSplit<>(split);
			final LeftRightSplit<L> duplicatedSplit = newSplit.addStatement(transition, Direction.MIDDLE);
			if (!newSplit.containsContradiction()) {
				if (OPTIMIZE_DEAD_ENDS && newSplit.willNeverContradict()) {
					return null;
				}
				newLeftRightSplits.add(newSplit);
			}
			if (duplicatedSplit != null && !duplicatedSplit.containsContradiction()) {
				if (OPTIMIZE_DEAD_ENDS && duplicatedSplit.willNeverContradict()) {
					return null;
				}
				newLeftRightSplits.add(duplicatedSplit);
			}
		}

		if (mLastStatement != null) {
			boolean done = false;

			for (final IProgramVar var : DataStructureUtils
					.intersection(mLastStatement.getTransformula().getInVars().keySet(), writes)) {
				// RWC
				final DependencyRank dr = mVariables.get(var);
				if (dr != null && dr.compareTo(deprank) <= 0) {
					done = true;
					deprank = deprank.getMax(lastStDeprank.add(rank));
					dependentOnLast = true;
				}
			}

			if (!done) {
				for (final IProgramVar var : DataStructureUtils
						.intersection(mLastStatement.getTransformula().getInVars().keySet(), writes)) {
					// TODO: WRWC
					deprank = deprank.getMax(lastStDeprank.add(rank));
					dependentOnLast = true;
				}
			}

			if (!done) {
				for (final IProgramVar var : DataStructureUtils
						.intersection(mLastStatement.getTransformula().getOutVars().keySet(), writes)) {
					if (lastStDeprank.compareTo(deprank) > 0) {
						deprank = deprank.getMax(lastStDeprank.add(rank));
						final LeftRightSplit<L> split = new LeftRightSplit<>();
						split.addStatement(mLastStatement, Direction.RIGHT);
						split.addStatement(transition, Direction.LEFT);
						newLeftRightSplits.add(split);
						dependentOnLast = true;
					}
				}
			}
		}

		if (!dependentOnLast && mLastStatement.hashCode() > rank) {
			return null;
		}

		if (!dependentOnLast && lastStDeprank.containsRank(rank)) {
			deprank = deprank.getMax(lastStDeprank.add(rank));
		}

		if (lastStDeprank != null && lastStDeprank.compareTo(deprank) > 0) {
			return null;
		}

		final Map<String, DependencyRank> newThreads = new HashMap<>(mThreads);
		final Map<IProgramVar, DependencyRank> newVariables = new HashMap<>(mVariables);
		final Map<IProgramVar, L> newLastWriteSt = new HashMap<>(mLastWriteSt);

		for (final String thread : getThreadId(transition)) {
			newThreads.put(thread, deprank);
		}
		for (final IProgramVar var : writes) {
			newVariables.put(var, deprank);
			newLastWriteSt.put(var, transition);
		}

		return new McrState<>(successor, newThreads, newVariables, newLastWriteSt, transition, newLeftRightSplits);
	}

	/**
	 * Checks whether the state contains no left-right splits.
	 *
	 * @return true if the state contains no left-right splits.
	 */
	@Override
	public boolean isRepresentative() {
		return mLeftRightSplits.isEmpty();
	}

	@Override
	public int hashCode() {
		return Objects.hash(mLastStatement, mLastWriteSt, mLeftRightSplits, mOldState, mThreads, mVariables);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final McrState<?> other = (McrState<?>) obj;
		return Objects.equals(mLastStatement, other.mLastStatement) && Objects.equals(mLastWriteSt, other.mLastWriteSt)
				&& Objects.equals(mLeftRightSplits, other.mLeftRightSplits)
				&& Objects.equals(mOldState, other.mOldState) && Objects.equals(mThreads, other.mThreads)
				&& Objects.equals(mVariables, other.mVariables);
	}

	@Override
	public String toString() {
		return "McrState [mOldState=" + mOldState + ", mThreads=" + mThreads + ", mVariables=" + mVariables
				+ ", mLastWriteSt=" + mLastWriteSt + ", mLastStatement=" + mLastStatement + ", mLeftRightSplits="
				+ mLeftRightSplits + "]";
	}

	@Override
	public Term getFormula() {
		return mOldState.getFormula();
	}

	@Override
	public Term getClosedFormula() {
		return mOldState.getClosedFormula();
	}

	@Override
	public String[] getProcedures() {
		return mOldState.getProcedures();
	}

	@Override
	public Set<IProgramVar> getVars() {
		return mOldState.getVars();
	}

	@Override
	public IcfgLocation[] getProgramPoints() {
		return mOldState.getProgramPoints();
	}

	@Override
	public Set<IProgramConst> getConstants() {
		return mOldState.getConstants();
	}

	@Override
	public Set<IProgramFunction> getFunctions() {
		return mOldState.getFunctions();
	}
}
