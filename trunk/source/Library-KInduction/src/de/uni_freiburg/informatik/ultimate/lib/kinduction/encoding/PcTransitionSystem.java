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
package de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.LoopTreeFormulaBuilder.Checkpoint;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.LoopTreeFormulaBuilder.LoopTree;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.LoopTreeFormulaBuilder.Scope;

/**
 * A transition system made from a {@link LoopTree}: the state is the program variables plus a program counter
 * {@code pc}. The values of {@code pc} are
 * <ul>
 * <li>{@link #INIT}: program start, has no incoming transition,
 * <li>{@link #FINAL}: the error/accepting states, has only a self loop (stutter), so "an error is reachable within at
 * most k steps" is the same as "{@code pc = FINAL} after exactly k steps",
 * <li>every head of every loop (all nesting depths): a reducible loop contributes one, a loop with irreducible
 * control flow one per entry state,
 * <li>every "waypoint": a state outside a loop that a {@code break} out of the loop can jump to.
 * </ul>
 * Every edge of every scope of the tree is one transition, from the node of its source checkpoint to the node of its
 * target checkpoint, labelled with the edge's formula. Every program execution is a sequence of such transitions,
 * because it is cut at each visit of a loop head. One transition can stand for many letters, and at a call site for
 * a whole call-to-return span (see {@link ProcedureSummaries}); {@link KInductionCounterexampleBuilder} is what
 * turns a transition back into letters.
 * <p>
 * {@link #step} builds the relation between step {@code idx} and step {@code idx + 1}. Variables a transition does
 * not assign are explicitly kept equal (frame); one that is only an inVar is havoced, so it is not framed. Auxiliary
 * variables are instantiated separately for every transition and step. The pc and the transition ids are of the
 * {@link CounterSort} of the program.
 *
 * @param <STATE>
 *            state type of the automaton
 */
public class PcTransitionSystem<STATE> {

	public static final int INIT = 0;
	public static final int FINAL = 1;

	private final List<Transition<STATE>> mTransitions = new ArrayList<>();
	private final Map<STATE, Integer> mHeadNodes = new LinkedHashMap<>();
	private final Map<STATE, Integer> mWaypointNodes = new LinkedHashMap<>();
	private final Set<IProgramVar> mVars = new LinkedHashSet<>();
	private final Set<IProgramVar> mOldVars = new LinkedHashSet<>();
	private int mNumNodes = 2;
	private int mStutterTransitionId = -1;
	private final CounterSort mCounterSort;

	/**
	 * Supplies the terms for one unrolling of the system, either constants (for a solver query) or term variables
	 * (to build a formula with quantifiers).
	 */
	public interface StepVars {
		/** The value of the program variable in step {@code idx}. */
		Term var(IProgramVar pv, int idx);

		/** The program counter in step {@code idx}. */
		Term pc(int idx);

		/** The auxiliary variable of transition {@code transitionId}, as used between step {@code idx} and the next. */
		Term aux(int transitionId, TermVariable auxVar, int idx);

		/**
		 * A term that names which transition is taken between step {@code idx} and the next, so that a model can
		 * be asked for it. {@code null}, the default, encodes no selector at all and leaves {@link #step} exactly
		 * as it was.
		 */
		default Term sel(final int idx) {
			return null;
		}
	}

	/**
	 * One transition of the system: an edge of one scope's checkpoint graph, or the stutter self loop of
	 * {@link #FINAL}. Besides the pc nodes it remembers the automaton states the two checkpoints stand for, which
	 * is what lets a counterexample be reconstructed from a model.
	 */
	public static final class Transition<STATE> {
		private final int mId;
		private final int mFrom;
		private final int mTo;
		// null: identity (stutter)
		private final UnmodifiableTransFormula mFormula;
		// null for the stutter
		private final Scope<STATE> mScope;
		private final Checkpoint<STATE> mFromCheckpoint;
		private final Checkpoint<STATE> mToCheckpoint;
		private final Collection<STATE> mSourceStates;
		private final Collection<STATE> mTargetStates;

		Transition(final int id, final int from, final int to, final UnmodifiableTransFormula formula,
				final Scope<STATE> scope, final Checkpoint<STATE> fromCheckpoint,
				final Checkpoint<STATE> toCheckpoint, final Collection<STATE> sourceStates,
				final Collection<STATE> targetStates) {
			mId = id;
			mFrom = from;
			mTo = to;
			mFormula = formula;
			mScope = scope;
			mFromCheckpoint = fromCheckpoint;
			mToCheckpoint = toCheckpoint;
			mSourceStates = sourceStates;
			mTargetStates = targetStates;
		}

		public int getId() {
			return mId;
		}

		public int getFromNode() {
			return mFrom;
		}

		public int getToNode() {
			return mTo;
		}

		/** The transition relation, {@code null} for the stutter self loop of {@link PcTransitionSystem#FINAL}. */
		public UnmodifiableTransFormula getFormula() {
			return mFormula;
		}

		/** The scope this edge came from, {@code null} for the stutter. */
		public Scope<STATE> getScope() {
			return mScope;
		}

		/** The source checkpoint, {@code null} for the stutter. */
		public Checkpoint<STATE> getFromCheckpoint() {
			return mFromCheckpoint;
		}

		/** The target checkpoint, {@code null} for the stutter. */
		public Checkpoint<STATE> getToCheckpoint() {
			return mToCheckpoint;
		}

		/** The automaton states a letter path realising this transition can start in. */
		public Collection<STATE> getSourceStates() {
			return mSourceStates;
		}

		/** The automaton states a letter path realising this transition can end in. */
		public Collection<STATE> getTargetStates() {
			return mTargetStates;
		}

		public boolean isStutter() {
			return mFormula == null;
		}

		@Override
		public String toString() {
			if (isStutter()) {
				return "t" + mId + ": FINAL -> FINAL (stutter)";
			}
			return "t" + mId + ": " + mFrom + " -> " + mTo + " (" + mScope + ", " + mFromCheckpoint + " -> "
					+ mToCheckpoint + ")";
		}
	}

	public PcTransitionSystem(final LoopTree<STATE> tree, final CounterSort counterSort) {
		mCounterSort = counterSort;
		final List<Scope<STATE>> scopes = new ArrayList<>();
		scopes.add(tree.getRoot());
		for (final Scope<STATE> loop : tree.getLoops()) {
			for (final STATE head : loop.getHeads()) {
				mHeadNodes.put(head, mNumNodes++);
			}
			scopes.add(loop);
		}
		for (final Scope<STATE> scope : scopes) {
			for (final Map.Entry<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> from : scope
					.getEdges().entrySet()) {
				for (final Map.Entry<Checkpoint<STATE>, UnmodifiableTransFormula> to : from.getValue().entrySet()) {
					addTransition(scope, from.getKey(), to.getKey(), to.getValue());
				}
			}
		}
		mStutterTransitionId = mTransitions.size();
		mTransitions.add(new Transition<>(mStutterTransitionId, FINAL, FINAL, null, null, null, null,
				Collections.emptyList(), Collections.emptyList()));
	}

	private void addTransition(final Scope<STATE> scope, final Checkpoint<STATE> from, final Checkpoint<STATE> to,
			final UnmodifiableTransFormula formula) {
		mTransitions.add(new Transition<>(mTransitions.size(), nodeOf(from), nodeOf(to), formula,
				scope, from, to, scope.getCheckpointStates(from), scope.getCheckpointStates(to)));
		collectVars(formula.getInVars().keySet());
		collectVars(formula.getOutVars().keySet());
	}

	private void collectVars(final Set<IProgramVar> vars) {
		for (final IProgramVar pv : vars) {
			if (pv.isOldvar()) {
				mOldVars.add(pv);
			} else {
				mVars.add(pv);
			}
		}
	}

	private int nodeOf(final Checkpoint<STATE> checkpoint) {
		if (checkpoint.isInit() || checkpoint.isEnd()) {
			// An INIT or END checkpoint names its own head, so a scope with several heads maps to several nodes.
			// Only the root's INIT has none.
			final STATE head = checkpoint.getScopeHead();
			return head == null ? INIT : headNode(head, checkpoint);
		}
		if (checkpoint.isFinal()) {
			return FINAL;
		}
		if (checkpoint.isLoopHead()) {
			return headNode(checkpoint.getLoopHead(), checkpoint);
		}
		final STATE state = checkpoint.getEscapeState();
		final Integer head = mHeadNodes.get(state);
		if (head != null) {
			return head;
		}
		return mWaypointNodes.computeIfAbsent(state, k -> mNumNodes++);
	}

	/**
	 * The pc node of a loop head. A head that was never registered must not fall through to a fresh waypoint node:
	 * that would split one program point into two pc values and break the cut the whole encoding rests on.
	 */
	private int headNode(final STATE head, final Checkpoint<STATE> checkpoint) {
		final Integer node = mHeadNodes.get(head);
		if (node == null) {
			throw new IllegalStateException(
					"Checkpoint " + checkpoint + " names " + head + ", which is not a head of any loop of the tree");
		}
		return node;
	}

	/** The pc value of each head of each loop. */
	public Map<STATE, Integer> getHeadNodes() {
		return Collections.unmodifiableMap(mHeadNodes);
	}

	/** The non-old program variables that occur in some transition. */
	public Set<IProgramVar> getVars() {
		return Collections.unmodifiableSet(mVars);
	}

	/**
	 * The old variables that occur in some transition. They are not part of the state: {@link #instantiate} maps
	 * them to {@link IProgramVar#getDefaultConstant()}, which is shared by every step.
	 */
	public Set<IProgramVar> getOldVars() {
		return Collections.unmodifiableSet(mOldVars);
	}

	/** The pc value of each "waypoint", a state outside a loop that a break out of the loop can jump to. */
	public Map<STATE, Integer> getWaypointNodes() {
		return Collections.unmodifiableMap(mWaypointNodes);
	}

	public Transition<STATE> getTransition(final int id) {
		if (id < 0 || id >= mTransitions.size()) {
			throw new IllegalArgumentException(
					"no transition with id " + id + ", the system has " + mTransitions.size());
		}
		return mTransitions.get(id);
	}

	/** The id of the stutter self loop of {@link #FINAL}, the only transition leaving FINAL. */
	public int getStutterTransitionId() {
		return mStutterTransitionId;
	}

	public int getNumTransitions() {
		return mTransitions.size();
	}

	public int getNumNodes() {
		return mNumNodes;
	}

	/** The sort of the pc and of the transition ids. */
	public CounterSort getCounterSort() {
		return mCounterSort;
	}

	/** The term for the pc value {@code node}. */
	public Term pcValue(final Script script, final int node) {
		return mCounterSort.value(script, node);
	}

	/** The term that names transition {@code id} in a step selector, see {@link StepVars#sel(int)}. */
	public Term transitionIdValue(final Script script, final int id) {
		return mCounterSort.value(script, id);
	}

	/**
	 * The relation between step {@code idx} and step {@code idx + 1}: some transition is taken, i.e. pc and variables
	 * of the two steps fit to one of the transitions.
	 */
	public Term step(final int idx, final StepVars sv, final ManagedScript mgdScript) {
		final Script script = mgdScript.getScript();
		final List<Term> disjuncts = new ArrayList<>();
		final Term selector = sv.sel(idx);
		for (final Transition<STATE> t : mTransitions) {
			final List<Term> conjuncts = new ArrayList<>();
			conjuncts.add(SmtUtils.binaryEquality(script, sv.pc(idx), pcValue(script, t.mFrom)));
			conjuncts.add(SmtUtils.binaryEquality(script, sv.pc(idx + 1), pcValue(script, t.mTo)));
			if (selector != null) {
				// Pins a fresh, otherwise unconstrained constant to this disjunct's transition id, so a model
				// names the transition that was taken. Satisfiability is unchanged in both directions.
				conjuncts.add(SmtUtils.binaryEquality(script, selector, transitionIdValue(script, t.mId)));
			}
			final Set<IProgramVar> assigned = new LinkedHashSet<>();
			if (t.mFormula != null) {
				conjuncts.add(instantiate(t, idx, sv, mgdScript, assigned));
			}
			for (final IProgramVar pv : mVars) {
				if (!assigned.contains(pv)) {
					conjuncts.add(SmtUtils.binaryEquality(script, sv.var(pv, idx + 1), sv.var(pv, idx)));
				}
			}
			disjuncts.add(SmtUtils.and(script, conjuncts));
		}
		return SmtUtils.or(script, disjuncts);
	}

	private Term instantiate(final Transition<STATE> t, final int idx, final StepVars sv,
			final ManagedScript mgdScript, final Set<IProgramVar> assigned) {
		final UnmodifiableTransFormula tf = t.mFormula;
		final Map<Term, Term> substitution = new HashMap<>();
		for (final Map.Entry<IProgramVar, TermVariable> in : tf.getInVars().entrySet()) {
			final IProgramVar pv = in.getKey();
			substitution.put(in.getValue(), pv.isOldvar() ? pv.getDefaultConstant() : sv.var(pv, idx));
			if (!tf.getOutVars().containsKey(pv)) {
				// Read, then havoced: a variable that is only an inVar may have any value afterwards (see
				// TransFormulaUtils#computeAssignedVars). TransFormulaBuilder drops the outVar of an assigned
				// variable whose new value the formula does not constrain, so a composed loop body has such
				// variables. Framing them would keep their value and lose every run in which it changes.
				assigned.add(pv);
			}
		}
		for (final Map.Entry<IProgramVar, TermVariable> out : tf.getOutVars().entrySet()) {
			final IProgramVar pv = out.getKey();
			if (tf.getInVars().get(pv) == out.getValue()) {
				continue;
			}
			assigned.add(pv);
			substitution.put(out.getValue(),
					pv.isOldvar() && !tf.getAssignedVars().contains(pv) ? pv.getDefaultConstant()
							: sv.var(pv, idx + 1));
		}
		for (final TermVariable aux : tf.getAuxVars()) {
			substitution.put(aux, sv.aux(t.mId, aux, idx));
		}
		return PureSubstitution.apply(mgdScript, substitution, tf.getFormula());
	}
}
