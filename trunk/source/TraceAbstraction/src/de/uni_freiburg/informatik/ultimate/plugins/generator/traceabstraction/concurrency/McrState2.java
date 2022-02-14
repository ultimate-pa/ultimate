/*
 * Copyright (C) 2022 Dennis Wölfing
 * Copyright (C) 2022 University of Freiburg
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

import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.LeftRightSplit.Direction;

/**
 * All the information for MCR to be encoded in automaton states. Version that does not use dependency ranks.
 *
 * @author Dennis Wölfing
 *
 * @param <L>
 *            The letters of the automaton.
 * @param <S>
 *            The type of states in the input automaton.
 */
public class McrState2<L extends IIcfgTransition<?>> implements IMcrState<L> {
	private static final boolean OPTIMIZE_DEAD_ENDS = true;

	private final IMLPredicate mOldState;
	private final Set<LeftRightSplit<L>> mTemplates;
	private final Set<ReducingLeftRightSplit<L>> mSplits;

	/**
	 * Constructs a new McrState for the initial state.
	 *
	 * @param state
	 *            The initial state in the input automaton.
	 */
	public McrState2(final IMLPredicate state) {
		mOldState = state;
		mTemplates = Set.of(new LeftRightSplit<>());
		mSplits = new HashSet<>();
	}

	/**
	 * Constructs a new McrState.
	 *
	 * @param oldState
	 *            The state in the input automaton.
	 * @param templates
	 *            The set of template left-right splits.
	 * @param splits
	 *            The set of reducing left-right splits.
	 */
	public McrState2(final IMLPredicate oldState, final Set<LeftRightSplit<L>> templates,
			final Set<ReducingLeftRightSplit<L>> splits) {
		mOldState = oldState;
		mTemplates = templates;
		mSplits = splits;
	}

	@Override
	public IMLPredicate getOldState() {
		return mOldState;
	}

	private <SPLIT extends LeftRightSplit<L>> boolean addStatementToSplit(final SPLIT split, final L letter,
			final Direction direction, final Set<SPLIT> set, final boolean optimizeDeadEnds) {
		final SPLIT duplicate = (SPLIT) split.addStatement(letter, direction);
		if (!split.containsContradiction()) {
			if (optimizeDeadEnds && split.willNeverContradict()) {
				return false;
			}
			set.add(split);
		}
		if (duplicate != null && !duplicate.containsContradiction()) {
			if (optimizeDeadEnds && duplicate.willNeverContradict()) {
				return false;
			}
			set.add(split);
		}
		return true;
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
	public McrState2<L> getNextState(final L transition, final IMLPredicate successor, final Map<L, Integer> ranks,
			final boolean optimizeForkJoin, final boolean overapproximateWrwc) {
		final Set<LeftRightSplit<L>> newTemplates = new HashSet<>();
		final Set<ReducingLeftRightSplit<L>> newSplits = new HashSet<>();

		for (final LeftRightSplit<L> template : mTemplates) {
			final ReducingLeftRightSplit<L> split = new ReducingLeftRightSplit<>(template, ranks);
			split.moveLast(Direction.RIGHT);
			addStatementToSplit(split, transition, Direction.LEFT, newSplits, false);
		}

		for (final ReducingLeftRightSplit<L> split : mSplits) {
			final ReducingLeftRightSplit<L> copy = new ReducingLeftRightSplit<>(split, ranks);
			if (!addStatementToSplit(copy, transition, Direction.MIDDLE, newSplits, OPTIMIZE_DEAD_ENDS)) {
				return null;
			}
		}

		for (final LeftRightSplit<L> template : mTemplates) {
			final LeftRightSplit<L> copy = new LeftRightSplit<>(template);
			addStatementToSplit(copy, transition, Direction.MIDDLE, newTemplates, false);
		}

		return new McrState2<>(successor, newTemplates, newSplits);
	}

	/**
	 * Checks whether the state contains no left-right splits.
	 *
	 * @return true if the state contains no left-right splits.
	 */
	@Override
	public boolean isRepresentative() {
		return mSplits.isEmpty();
	}

	@Override
	public int hashCode() {
		return Objects.hash(mOldState, mSplits, mTemplates);
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
		final McrState2<?> other = (McrState2<?>) obj;
		return Objects.equals(mOldState, other.mOldState) && Objects.equals(mSplits, other.mSplits)
				&& Objects.equals(mTemplates, other.mTemplates);
	}

	@Override
	public String toString() {
		return "McrState2 [mOldState=" + mOldState + ", mTemplates=" + mTemplates + ", mSplits=" + mSplits + "]";
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
