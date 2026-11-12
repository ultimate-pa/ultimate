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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.IntPredicate;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.LoopTreeFormulaBuilder.Scope;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * A transition system made from a tree of {@link Scope}s: the state is the program variables plus a program counter
 * {@code pc}. The values of {@code pc} are
 * <ul>
 * <li>{@link #INIT}: program start, has no incoming transition,
 * <li>{@link #FINAL}: the error/accepting states, has only a self loop (stutter), so "an error is reachable within at
 * most k steps" is the same as "{@code pc = FINAL} after exactly k steps",
 * <li>every head of every loop (all nesting depths): a reducible loop contributes one, a loop with irreducible
 * control flow one per entry state,
 * <li>every "waypoint": a state outside a loop that a {@code break} out of the loop can jump to.
 * </ul>
 * One step goes from one pc value to the next along a path of one scope's cut graph. Every program execution is a
 * sequence of such steps, because it is cut at each visit of a loop head. {@link #getChainOfStep} reads the states
 * of a step back off a model.
 *
 * <h2>The formula of a step</h2>
 *
 * The cut graphs are acyclic, and the paths through them are not composed. {@link #step} instead gives every node
 * {@code n} of a cut graph one subformula, "a path from here ends in a pc value":
 *
 * <pre>
 *   F(n) = OR_(n is a target of pc value p) (pc' = p and outputs) or OR_(edge e from n to m) (e and joins(e) and F(m))
 *   step = OR_(source of pc value p) (pc = p and F(source))
 * </pre>
 *
 * Subformulas are shared, so a step is linear in the size of the cut graphs, however many paths they have. This is why
 * these terms are built without {@link SmtUtils}: it flattens nested conjunctions, which would undo that sharing.
 * <p>
 * Variables are in static single assignment form, per step. The <em>version</em> of a variable at a node is its value
 * at the start of the step, the constant an edge writes it to, or, where edges with different versions meet, a constant
 * of that node, which each of those edges sets ({@code joins(e)} above). On the path a model selects the versions hold
 * the path's values, and on any other path they are unconstrained. Together this is exactly the union of the paths: a
 * model has a chain of edges from the source to a target whose formulas all hold, and every path gives a model.
 * <p>
 * A variable only has to keep its value where that value can still be read. Where it cannot, {@link #step} for a query
 * leaves it unconstrained, see {@link Encoding}. This cannot change a query's answer, since such a value has no
 * influence on the rest of a run. The one exception is an injected invariant that mentions it, which then assumes less
 * than it could. The full-frame {@link #step(int, StepVars, ManagedScript)} is for everyone who needs the exact relation
 * between two states.
 * <p>
 * An old variable is not part of the state: a step starts with {@link IProgramVar#getDefaultConstant()}, and a call
 * inside the step gives it a version of its own.
 *
 * @param <STATE>
 *            state type of the automaton
 */
public class PcTransitionSystem<STATE> {

	public static final int INIT = 0;
	public static final int FINAL = 1;

	/** The owner of the version a variable has at the start of a step. */
	private static final int STEP_START = -1;

	private final Map<STATE, Integer> mHeadNodes = new LinkedHashMap<>();
	private final Map<STATE, Integer> mWaypointNodes = new LinkedHashMap<>();
	private final Set<IProgramVar> mVars = new LinkedHashSet<>();
	private final Set<IProgramVar> mOldVars = new LinkedHashSet<>();
	private final Set<IProgramVar> mAlwaysFramed;
	private final CounterSort mCounterSort;
	private int mNumNodes = 2;

	// The cut graphs of all scopes, shared with every transferred copy of this system: only the formulas differ. An edge
	// always leads to a later node of mDagNodes.
	private final List<DagNode> mDagNodes;
	private final List<DagNode> mSources;
	private final Map<Integer, Set<STATE>> mSourceStates;
	private final Map<Integer, Set<STATE>> mTargetStates;
	/** The state of each node of a cut graph, and of each source that starts at one state. Others have none. */
	private final Map<DagNode, STATE> mStateOfNode;
	private int mNextDagId;

	/** The formula of each edge, by {@link DagEdge#mFormulaIndex}. */
	private final List<UnmodifiableTransFormula> mFormulas = new ArrayList<>();
	/** {@link #mFormulas} as they are instantiated, computed the first time a step needs them. */
	private final Map<Integer, Term> mEncodedFormulas = new HashMap<>();
	private Encoding mQueryEncoding;
	private Encoding mFullFrameEncoding;

	/**
	 * Supplies the terms for one unrolling of the system, either constants (for a solver query) or term variables
	 * (to build a formula with quantifiers).
	 */
	public interface StepVars {
		/** The value of the program variable in step {@code idx}. */
		Term var(IProgramVar pv, int idx);

		/** The program counter in step {@code idx}. */
		Term pc(int idx);

		/**
		 * A value inside the step from {@code idx} to the next, one per {@code id} and {@code auxVar}: an auxiliary
		 * variable of an edge, or the version of a program variable at an edge or a node.
		 */
		Term aux(int id, TermVariable auxVar, int idx);
	}

	/** A node of a cut graph, or the start of a step in a scope (a source). */
	private static final class DagNode {
		private final int mId;
		private final int mPosition;
		private final List<DagEdge> mOutgoing = new ArrayList<>();
		private final List<DagEdge> mIncoming = new ArrayList<>();
		/** The pc values a path may end in at this node. */
		private final List<Integer> mTargetPcs = new ArrayList<>();
		/** The pc value this node starts a step from, {@code -1} if it is no source. */
		private final int mSourcePc;

		private DagNode(final int id, final int position, final int sourcePc) {
			mId = id;
			mPosition = position;
			mSourcePc = sourcePc;
		}
	}

	private static final class DagEdge {
		private final int mId;
		private final DagNode mSource;
		private final DagNode mTarget;
		/** {@code -1}: the empty path from a source to the node it starts at. */
		private final int mFormulaIndex;

		private DagEdge(final int id, final DagNode source, final DagNode target, final int formulaIndex) {
			mId = id;
			mSource = source;
			mTarget = target;
			mFormulaIndex = formulaIndex;
		}
	}

	/** The value of a variable inside a step: at its start, or a constant of the edge or node {@code owner}. */
	private record Version(IProgramVar var, int owner) {
	}

	/** An edge that leads to a node where versions meet says which one holds. */
	private record Join(Version atNode, Version onEdge) {
	}

	/** How an edge is instantiated, see {@link Encoding}. */
	private record EdgeCode(Map<TermVariable, Version> versions, List<Join> joins) {
	}

	/** A path that ends in {@code pc}, with the version of every variable the state there has to keep. */
	private record TargetCode(int pc, List<Version> outputs) {
	}

	/** All paths between two pc values, see {@link PcTransitionSystem#composeSteps}. */
	private record ComposedStep(int from, int to, UnmodifiableTransFormula formula) {
	}

	/**
	 * How the edges and targets are instantiated, see {@link EncodingBuilder}. There is one for the queries, in which only
	 * live variables are kept, and one with the full frame.
	 */
	private record Encoding(Map<DagEdge, EdgeCode> edgeCode, Map<DagNode, List<TargetCode>> targetCode,
			List<Set<IProgramVar>> liveAtPc, Set<Version> innerVersions) {
		private long numberOfFrameEqualities() {
			long result = 0;
			for (final EdgeCode code : edgeCode.values()) {
				result += code.joins().size();
			}
			for (final List<TargetCode> targets : targetCode.values()) {
				for (final TargetCode target : targets) {
					result += target.outputs().size();
				}
			}
			return result;
		}
	}

	/**
	 * Computes the versions of all variables at all nodes, and what follows from them for the edges and targets. What it
	 * holds besides the result is only needed for that, so it does not stay on the heap during the queries.
	 * <p>
	 * A variable is live at a node if a path from there reads it before writing it. For an edge {@code e} from n to m,
	 * {@code live(n)} contains {@code reads(e) + (live(m) - writes(e))}. A node that is a target of a pc value has what
	 * is live at the sources of that value. This is the usual fixed point, whose only cycles are through the pc values,
	 * since every cut graph is acyclic. A variable of {@link #mAlwaysFramed} is live at every pc value.
	 */
	private final class EncodingBuilder {
		private final Map<DagEdge, EdgeCode> mEdgeCode = new HashMap<>();
		private final Map<DagNode, List<TargetCode>> mTargetCode = new HashMap<>();

		private final List<IProgramVar> mIndexedVars = new ArrayList<>();
		private final Map<IProgramVar, Integer> mVarIndex = new HashMap<>();
		private final List<Set<TermVariable>> mFreeVars = new ArrayList<>();
		private final List<BitSet> mReads = new ArrayList<>();
		private final List<BitSet> mWrites = new ArrayList<>();

		private Encoding build(final boolean fullFrame) {
			// The state variables come first, so that they are the bits below mVars.size().
			for (final IProgramVar pv : mVars) {
				mVarIndex.put(pv, mIndexedVars.size());
				mIndexedVars.add(pv);
			}
			for (final IProgramVar pv : mOldVars) {
				mVarIndex.put(pv, mIndexedVars.size());
				mIndexedVars.add(pv);
			}
			for (final UnmodifiableTransFormula tf : mFormulas) {
				final Set<TermVariable> free = new HashSet<>(Arrays.asList(tf.getFormula().getFreeVars()));
				final BitSet reads = new BitSet();
				for (final Map.Entry<IProgramVar, TermVariable> in : tf.getInVars().entrySet()) {
					if (free.contains(in.getValue())) {
						reads.set(mVarIndex.get(in.getKey()));
					}
				}
				final BitSet writes = new BitSet();
				for (final IProgramVar pv : assignedVars(tf)) {
					writes.set(mVarIndex.get(pv));
				}
				mFreeVars.add(free);
				mReads.add(reads);
				mWrites.add(writes);
			}
			final BitSet stateVars = new BitSet();
			stateVars.set(0, mVars.size());
			final BitSet[] liveAtPc = new BitSet[mNumNodes];
			final BitSet[] liveAtNode = new BitSet[mDagNodes.size()];
			if (fullFrame) {
				final BitSet allVars = new BitSet();
				allVars.set(0, mIndexedVars.size());
				Arrays.fill(liveAtPc, stateVars);
				Arrays.fill(liveAtNode, allVars);
			} else {
				computeLiveness(liveAtPc, liveAtNode, stateVars);
			}
			computeVersions(liveAtPc, liveAtNode);
			final List<Set<IProgramVar>> liveVars = new ArrayList<>(liveAtPc.length);
			for (final BitSet live : liveAtPc) {
				final Set<IProgramVar> vars = new LinkedHashSet<>();
				for (int i = live.nextSetBit(0); i >= 0; i = live.nextSetBit(i + 1)) {
					vars.add(mIndexedVars.get(i));
				}
				liveVars.add(Collections.unmodifiableSet(vars));
			}
			final Set<Version> innerVersions = new LinkedHashSet<>();
			for (final EdgeCode code : mEdgeCode.values()) {
				innerVersions.addAll(code.versions().values());
				for (final Join join : code.joins()) {
					innerVersions.add(join.atNode());
					innerVersions.add(join.onEdge());
				}
			}
			innerVersions.removeIf(version -> version.owner() == STEP_START || version.var().isOldvar());
			return new Encoding(mEdgeCode, mTargetCode, Collections.unmodifiableList(liveVars), innerVersions);
		}

		private void computeLiveness(final BitSet[] liveAtPc, final BitSet[] liveAtNode, final BitSet stateVars) {
			final BitSet alwaysLive = new BitSet();
			for (final IProgramVar pv : mAlwaysFramed) {
				alwaysLive.set(mVarIndex.get(pv));
			}
			for (int pc = 0; pc < liveAtPc.length; pc++) {
				liveAtPc[pc] = (BitSet) alwaysLive.clone();
			}
			boolean changed = true;
			while (changed) {
				changed = false;
				for (int position = mDagNodes.size() - 1; position >= 0; position--) {
					final DagNode node = mDagNodes.get(position);
					final BitSet live = new BitSet();
					for (final int pc : node.mTargetPcs) {
						live.or(liveAtPc[pc]);
					}
					for (final DagEdge edge : node.mOutgoing) {
						final BitSet behind = (BitSet) liveAtNode[edge.mTarget.mPosition].clone();
						if (edge.mFormulaIndex >= 0) {
							behind.andNot(mWrites.get(edge.mFormulaIndex));
							behind.or(mReads.get(edge.mFormulaIndex));
						}
						live.or(behind);
					}
					liveAtNode[position] = live;
					if (node.mSourcePc >= 0) {
						final BitSet atPc = liveAtPc[node.mSourcePc];
						final int before = atPc.cardinality();
						final BitSet stateVarsHere = (BitSet) live.clone();
						stateVarsHere.and(stateVars);
						atPc.or(stateVarsHere);
						changed |= atPc.cardinality() != before;
					}
				}
			}
		}

		private void computeVersions(final BitSet[] liveAtPc, final BitSet[] liveAtNode) {
			final Version[] atStepStart = new Version[mIndexedVars.size()];
			for (int i = 0; i < atStepStart.length; i++) {
				atStepStart[i] = new Version(mIndexedVars.get(i), STEP_START);
			}
			final Version[][] versions = new Version[mDagNodes.size()][];
			// How many edges still need the versions of a node, which are of no use after that.
			final int[] pending = new int[mDagNodes.size()];
			for (final DagNode node : mDagNodes) {
				pending[node.mPosition] = node.mOutgoing.size();
			}
			for (final DagNode node : mDagNodes) {
				final Version[] here;
				if (node.mIncoming.isEmpty()) {
					here = atStepStart;
				} else {
					here = new Version[atStepStart.length];
					final BitSet live = liveAtNode[node.mPosition];
					for (int i = live.nextSetBit(0); i >= 0; i = live.nextSetBit(i + 1)) {
						here[i] = meet(node, i, versions);
					}
					for (final DagEdge edge : node.mIncoming) {
						final int source = edge.mSource.mPosition;
						if (--pending[source] == 0) {
							versions[source] = null;
						}
					}
				}
				if (pending[node.mPosition] > 0) {
					versions[node.mPosition] = here;
				}
				for (final DagEdge edge : node.mOutgoing) {
					mEdgeCode.put(edge, edgeCode(edge, here));
				}
				if (!node.mTargetPcs.isEmpty()) {
					final List<TargetCode> targets = new ArrayList<>(node.mTargetPcs.size());
					for (final int pc : node.mTargetPcs) {
						final List<Version> outputs = new ArrayList<>();
						final BitSet live = liveAtPc[pc];
						for (int i = live.nextSetBit(0); i >= 0; i = live.nextSetBit(i + 1)) {
							outputs.add(here[i]);
						}
						targets.add(new TargetCode(pc, outputs));
					}
					mTargetCode.put(node, targets);
				}
			}
		}

		/** The version of the variable {@code i} at {@code node}, adding the joins it takes to the edges into it. */
		private Version meet(final DagNode node, final int i, final Version[][] versions) {
			Version common = null;
			boolean differ = false;
			for (final DagEdge edge : node.mIncoming) {
				final Version behind = behind(edge, i, versions[edge.mSource.mPosition]);
				if (common != null && !common.equals(behind)) {
					differ = true;
				}
				common = behind;
			}
			if (!differ) {
				return common;
			}
			final Version joined = new Version(mIndexedVars.get(i), node.mId);
			for (final DagEdge edge : node.mIncoming) {
				mEdgeCode.get(edge).joins().add(new Join(joined, behind(edge, i, versions[edge.mSource.mPosition])));
			}
			return joined;
		}

		private Version behind(final DagEdge edge, final int i, final Version[] before) {
			if (edge.mFormulaIndex >= 0 && mWrites.get(edge.mFormulaIndex).get(i)) {
				return new Version(mIndexedVars.get(i), edge.mId);
			}
			return before[i];
		}

		private EdgeCode edgeCode(final DagEdge edge, final Version[] before) {
			final Map<TermVariable, Version> versions = new HashMap<>();
			if (edge.mFormulaIndex >= 0) {
				final UnmodifiableTransFormula tf = mFormulas.get(edge.mFormulaIndex);
				final Set<TermVariable> free = mFreeVars.get(edge.mFormulaIndex);
				for (final Map.Entry<IProgramVar, TermVariable> in : tf.getInVars().entrySet()) {
					if (free.contains(in.getValue())) {
						versions.put(in.getValue(), before[mVarIndex.get(in.getKey())]);
					}
				}
				for (final Map.Entry<IProgramVar, TermVariable> out : tf.getOutVars().entrySet()) {
					if (tf.getInVars().get(out.getKey()) != out.getValue() && free.contains(out.getValue())) {
						versions.put(out.getValue(), new Version(out.getKey(), edge.mId));
					}
				}
			}
			return new EdgeCode(versions, new ArrayList<>());
		}
	}

	/**
	 * What a formula writes: what it has an outVar of that is not its inVar, and what it only has an inVar of. The latter
	 * means the variable is havoced, see {@code TransFormulaUtils#computeAssignedVars}: {@code TransFormulaBuilder} drops
	 * the outVar of an assigned variable whose new value the formula does not constrain. An old variable that is only an
	 * inVar is only read, since only a call changes the snapshot.
	 */
	private static Set<IProgramVar> assignedVars(final UnmodifiableTransFormula tf) {
		final Set<IProgramVar> result = new LinkedHashSet<>();
		for (final IProgramVar pv : tf.getInVars().keySet()) {
			if (!tf.getOutVars().containsKey(pv) && !pv.isOldvar()) {
				result.add(pv);
			}
		}
		for (final Map.Entry<IProgramVar, TermVariable> out : tf.getOutVars().entrySet()) {
			if (tf.getInVars().get(out.getKey()) != out.getValue()) {
				result.add(out.getKey());
			}
		}
		return result;
	}

	/**
	 * @param counterSort
	 *            the sort of the program's counters; the pc gets it, narrowed to the pc values of this system
	 * @param alwaysFramed
	 *            the variables that have to keep their value in every step of a query, even where nothing reads it,
	 *            because their value is read off a model
	 */
	public PcTransitionSystem(final Script script, final Scope<STATE> root, final CounterSort counterSort,
			final Set<IProgramVar> alwaysFramed) {
		mAlwaysFramed = alwaysFramed;
		mDagNodes = new ArrayList<>();
		mSources = new ArrayList<>();
		mSourceStates = new HashMap<>();
		mTargetStates = new HashMap<>();
		mStateOfNode = new HashMap<>();
		final List<Scope<STATE>> scopes = new ArrayList<>();
		scopes.add(root);
		for (final Scope<STATE> loop : root.loops()) {
			for (final STATE head : loop.heads()) {
				mHeadNodes.put(head, mNumNodes++);
			}
			scopes.add(loop);
		}
		for (final Scope<STATE> scope : scopes) {
			addScope(scope);
		}
		mCounterSort = counterSort.narrowedTo(script, mNumNodes - 1);
		for (final Map.Entry<STATE, Integer> waypoint : mWaypointNodes.entrySet()) {
			// A run that jumps to a waypoint without a way on would silently end there, which proves too much.
			if (!mSourceStates.containsKey(waypoint.getValue())) {
				throw new IllegalStateException("The waypoint " + waypoint.getKey() + " is no source of any scope");
			}
		}
	}

	private PcTransitionSystem(final PcTransitionSystem<STATE> original, final CounterSort counterSort) {
		mCounterSort = counterSort;
		// Only for reading a model, which nobody does on a copy.
		mAlwaysFramed = Collections.emptySet();
		mDagNodes = original.mDagNodes;
		mSources = original.mSources;
		mSourceStates = original.mSourceStates;
		mTargetStates = original.mTargetStates;
		mStateOfNode = original.mStateOfNode;
		mHeadNodes.putAll(original.mHeadNodes);
		mWaypointNodes.putAll(original.mWaypointNodes);
		mNumNodes = original.mNumNodes;
	}

	/**
	 * This system for another script, so that whoever reasons about the same program there need not build it again:
	 * the same pc nodes and cut graphs, with every formula replaced by its copy. The states are this system's, they
	 * only serve to reconstruct a counterexample.
	 *
	 * @param transferFormula
	 *            copies a formula of this system to the other script, together with its program variables
	 * @param counterSort
	 *            {@link #getCounterSort()} over the other script
	 */
	public PcTransitionSystem<STATE> transfer(final UnaryOperator<UnmodifiableTransFormula> transferFormula,
			final CounterSort counterSort) {
		final PcTransitionSystem<STATE> result = new PcTransitionSystem<>(this, counterSort);
		// The edges of the copies of a procedure share their formulas, and a formula must be constructed only once on a
		// script, since its constructor declares a constant per auxiliary variable.
		final Map<UnmodifiableTransFormula, UnmodifiableTransFormula> copies = new IdentityHashMap<>();
		for (final UnmodifiableTransFormula formula : mFormulas) {
			final UnmodifiableTransFormula copy = copies.computeIfAbsent(formula, transferFormula);
			result.mFormulas.add(copy);
			result.collectVars(copy);
		}
		return result;
	}

	private void addScope(final Scope<STATE> scope) {
		final Map<DagNode, List<Pair<UnmodifiableTransFormula, STATE>>> sources = new LinkedHashMap<>();
		if (scope.isRoot()) {
			final List<Pair<UnmodifiableTransFormula, STATE>> starts = new ArrayList<>();
			for (final STATE start : scope.programStarts()) {
				starts.add(new Pair<>(null, start));
			}
			sources.put(newSource(INIT, scope.programStarts()), starts);
		}
		for (final Map.Entry<STATE, List<Pair<UnmodifiableTransFormula, STATE>>> source : scope.sources().entrySet()) {
			final DagNode sourceNode = newSource(pcOf(source.getKey()), Collections.singleton(source.getKey()));
			mStateOfNode.put(sourceNode, source.getKey());
			sources.put(sourceNode, source.getValue());
		}
		final Map<STATE, DagNode> nodes = new HashMap<>();
		for (final STATE state : scope.cutGraph().keySet()) {
			final DagNode node = newDagNode(-1);
			mStateOfNode.put(node, state);
			nodes.put(state, node);
		}
		for (final Map.Entry<DagNode, List<Pair<UnmodifiableTransFormula, STATE>>> source : sources.entrySet()) {
			for (final Pair<UnmodifiableTransFormula, STATE> first : source.getValue()) {
				addDagEdge(source.getKey(), first.getFirst(), nodeOfState(nodes, first.getSecond()));
			}
		}
		for (final Map.Entry<STATE, List<Pair<UnmodifiableTransFormula, STATE>>> from : scope.cutGraph().entrySet()) {
			for (final Pair<UnmodifiableTransFormula, STATE> edge : from.getValue()) {
				addDagEdge(nodes.get(from.getKey()), edge.getFirst(), nodeOfState(nodes, edge.getSecond()));
			}
		}
		for (final Scope<STATE> child : scope.children()) {
			for (final STATE head : child.heads()) {
				addTarget(nodes, pcOf(head), head);
			}
		}
		for (final STATE head : scope.heads()) {
			addTarget(nodes, pcOf(head), head);
		}
		for (final STATE state : scope.finals()) {
			addTarget(nodes, FINAL, state);
		}
		for (final STATE escape : scope.escapes()) {
			addTarget(nodes, pcOf(escape), escape);
		}
	}

	private DagNode newSource(final int pc, final Set<STATE> states) {
		final DagNode node = newDagNode(pc);
		mSources.add(node);
		mSourceStates.computeIfAbsent(pc, k -> new LinkedHashSet<>()).addAll(states);
		return node;
	}

	private void addTarget(final Map<STATE, DagNode> nodes, final int pc, final STATE state) {
		mTargetStates.computeIfAbsent(pc, k -> new LinkedHashSet<>()).add(state);
		nodeOfState(nodes, state).mTargetPcs.add(pc);
	}

	private DagNode nodeOfState(final Map<STATE, DagNode> nodes, final STATE state) {
		final DagNode node = nodes.get(state);
		if (node == null) {
			throw new IllegalStateException(state + " is not a node of the cut graph it is used in");
		}
		return node;
	}

	private DagNode newDagNode(final int sourcePc) {
		final DagNode node = new DagNode(mNextDagId++, mDagNodes.size(), sourcePc);
		mDagNodes.add(node);
		return node;
	}

	private void addDagEdge(final DagNode from, final UnmodifiableTransFormula formula, final DagNode to) {
		int formulaIndex = -1;
		if (formula != null) {
			formulaIndex = mFormulas.size();
			mFormulas.add(formula);
			collectVars(formula);
		}
		final DagEdge edge = new DagEdge(mNextDagId++, from, to, formulaIndex);
		from.mOutgoing.add(edge);
		to.mIncoming.add(edge);
	}

	private void collectVars(final UnmodifiableTransFormula formula) {
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

	/**
	 * The pc value of a state a step starts or ends at: its own if it is a head of a loop, otherwise that of a waypoint.
	 * The constructor has numbered the heads of all loops of the tree by now.
	 */
	private int pcOf(final STATE state) {
		final Integer head = mHeadNodes.get(state);
		return head != null ? head : mWaypointNodes.computeIfAbsent(state, k -> mNumNodes++);
	}

	/**
	 * The variables a state with this pc value has to keep in a query, because a path from there reads them before it
	 * writes them (and those of {@code alwaysFramed}). Their values in a model of a query are the values of the path
	 * the model took; every other variable is unconstrained there, see the class javadoc.
	 */
	public Set<IProgramVar> getLiveVars(final int pc) {
		return queryEncoding().liveAtPc().get(pc);
	}

	/**
	 * The constants that hold a program variable's value inside step {@code idx} of a query: its version at an edge
	 * that writes it and at a node where versions meet. On the path a model takes they are the path's values, on every
	 * other path they are arbitrary - so they are good guesses for a value, nothing more. Old variables are left out.
	 *
	 * @param sv
	 *            the constants of the query; a version it has no constant for ({@code null}) is skipped
	 */
	public Map<IProgramVar, List<Term>> getVersionConstants(final int idx, final StepVars sv) {
		final Map<IProgramVar, List<Term>> result = new LinkedHashMap<>();
		for (final Version version : queryEncoding().innerVersions()) {
			final Term constant = sv.aux(version.owner(), version.var().getTermVariable(), idx);
			if (constant != null) {
				result.computeIfAbsent(version.var(), k -> new ArrayList<>()).add(constant);
			}
		}
		return result;
	}

	/**
	 * The constants that hold the auxiliary variables of the edges inside step {@code idx} of a query, by auxiliary
	 * variable. Where an edge was composed from several transitions, these are the values its variables had in
	 * between, e.g. a variable that a chain assigns and havocs again. Like {@link #getVersionConstants}, they are the
	 * path's values on the path a model takes and arbitrary elsewhere.
	 *
	 * @param sv
	 *            the constants of the query; an auxiliary variable it has no constant for ({@code null}) is skipped
	 */
	public Map<TermVariable, List<Term>> getAuxConstants(final int idx, final StepVars sv) {
		final Map<TermVariable, List<Term>> result = new LinkedHashMap<>();
		for (final DagNode node : mDagNodes) {
			for (final DagEdge edge : node.mOutgoing) {
				if (edge.mFormulaIndex < 0) {
					continue;
				}
				for (final TermVariable aux : mFormulas.get(edge.mFormulaIndex).getAuxVars()) {
					final Term constant = sv.aux(edge.mId, aux, idx);
					if (constant != null) {
						result.computeIfAbsent(aux, k -> new ArrayList<>()).add(constant);
					}
				}
			}
		}
		return result;
	}

	/**
	 * The chain of states a model of a query takes in the step from state {@code idx} to the next. The model satisfies
	 * {@code F(source)} (see the class javadoc), so it has a chain of edges whose formulas all hold up to a target of
	 * {@code toPc}, and every such chain is a path of the program. It is found by walking the cut graph and asking the
	 * model about the edges one by one, so only the edges next to the chain are looked at. An edge that holds can still
	 * lead to a node from which no chain goes on, since the versions off the model's path are arbitrary; the walk then
	 * goes back and takes another edge.
	 *
	 * @param fromPc
	 *            the pc value of state {@code idx} in the model
	 * @param toPc
	 *            the pc value of state {@code idx + 1} in the model
	 * @param sv
	 *            the constants of the query, see {@link IndexedConstantVars#declaredOnly()}
	 * @param holdsInModel
	 *            the value of a closed formula over these constants in the model
	 * @return the states of the chain in order. It does not start with a state if the step starts at {@link #INIT}.
	 * @throws IllegalStateException
	 *             if there is no such chain, in which case the model does not satisfy the step
	 */
	public List<STATE> getChainOfStep(final int idx, final int fromPc, final int toPc, final StepVars sv,
			final ManagedScript mgdScript, final Predicate<Term> holdsInModel) {
		final StepVars declared = requireDeclared(sv);
		final Encoding encoding = queryEncoding();
		final boolean[] leadsToTarget = nodesThatLeadTo(toPc, encoding);
		final Set<DagNode> dead = new HashSet<>();
		for (int position = 0; position < leadsToTarget.length; position++) {
			if (!leadsToTarget[position]) {
				dead.add(mDagNodes.get(position));
			}
		}
		for (final DagNode source : mSources) {
			if (source.mSourcePc != fromPc) {
				continue;
			}
			final List<DagNode> chain = walkFrom(source, encoding, idx, toPc, declared, mgdScript, holdsInModel, dead);
			if (chain != null) {
				final List<STATE> states = new ArrayList<>(chain.size());
				for (final DagNode node : chain) {
					final STATE state = mStateOfNode.get(node);
					if (state != null) {
						states.add(state);
					}
				}
				return states;
			}
		}
		throw new IllegalStateException("The model of the query has no chain of edges from pc value " + fromPc
				+ " to pc value " + toPc + " in step " + idx + ", so it does not satisfy the step");
	}

	/**
	 * @return by position in {@link #mDagNodes}, whether a path from the node can end in a target of {@code toPc}. Any
	 *         other node has no place in a step that ends in {@code toPc}. A query may not even have encoded it, as
	 *         {@link #encode} leaves out what leads only to pc values the step cannot end in, so that the constants of
	 *         its edges do not exist.
	 */
	private boolean[] nodesThatLeadTo(final int toPc, final Encoding encoding) {
		final boolean[] result = new boolean[mDagNodes.size()];
		for (int position = mDagNodes.size() - 1; position >= 0; position--) {
			final DagNode node = mDagNodes.get(position);
			for (final TargetCode target : encoding.targetCode().getOrDefault(node, Collections.emptyList())) {
				result[position] |= target.pc() == toPc;
			}
			for (final DagEdge edge : node.mOutgoing) {
				result[position] |= result[edge.mTarget.mPosition];
			}
		}
		return result;
	}

	/** @return the nodes of a chain from {@code source} that ends in a target of {@code toPc}, or null */
	private List<DagNode> walkFrom(final DagNode source, final Encoding encoding, final int idx, final int toPc,
			final StepVars sv, final ManagedScript mgdScript, final Predicate<Term> holdsInModel,
			final Set<DagNode> dead) {
		if (dead.contains(source)) {
			return null;
		}
		final List<DagNode> chain = new ArrayList<>();
		final Deque<Iterator<DagEdge>> pending = new ArrayDeque<>();
		chain.add(source);
		pending.addLast(source.mOutgoing.iterator());
		while (!pending.isEmpty()) {
			final Iterator<DagEdge> edges = pending.peekLast();
			if (!edges.hasNext()) {
				dead.add(chain.remove(chain.size() - 1));
				pending.removeLast();
				continue;
			}
			final DagEdge edge = edges.next();
			if (dead.contains(edge.mTarget) || !holdsInModel.test(edgeGuard(edge, encoding, idx, sv, mgdScript))) {
				continue;
			}
			chain.add(edge.mTarget);
			if (endsAt(edge.mTarget, encoding, idx, toPc, sv, mgdScript, holdsInModel)) {
				return chain;
			}
			pending.addLast(edge.mTarget.mOutgoing.iterator());
		}
		return null;
	}

	/** What {@link #encode} says about {@code edge} itself: its formula and its joins, without what comes after it. */
	private Term edgeGuard(final DagEdge edge, final Encoding encoding, final int idx, final StepVars sv,
			final ManagedScript mgdScript) {
		final Script script = mgdScript.getScript();
		final EdgeCode code = encoding.edgeCode().get(edge);
		final List<Term> conjuncts = new ArrayList<>();
		if (edge.mFormulaIndex >= 0) {
			conjuncts.add(instantiate(edge, code, idx, sv, mgdScript));
		}
		for (final Join join : code.joins()) {
			conjuncts.add(
					SmtUtils.binaryEquality(script, termOf(join.atNode(), sv, idx), termOf(join.onEdge(), sv, idx)));
		}
		return and(script, conjuncts);
	}

	private boolean endsAt(final DagNode node, final Encoding encoding, final int idx, final int toPc, final StepVars sv,
			final ManagedScript mgdScript, final Predicate<Term> holdsInModel) {
		final Script script = mgdScript.getScript();
		for (final TargetCode target : encoding.targetCode().getOrDefault(node, Collections.emptyList())) {
			if (target.pc() != toPc) {
				continue;
			}
			final List<Term> conjuncts = new ArrayList<>();
			for (final Version output : target.outputs()) {
				conjuncts.add(SmtUtils.binaryEquality(script, sv.var(output.var(), idx + 1), termOf(output, sv, idx)));
			}
			if (holdsInModel.test(and(script, conjuncts))) {
				return true;
			}
		}
		return false;
	}

	/** {@code sv}, except that a constant it does not have is an error instead of {@code null}. */
	private static StepVars requireDeclared(final StepVars sv) {
		return new StepVars() {
			@Override
			public Term var(final IProgramVar pv, final int idx) {
				return require(sv.var(pv, idx), pv);
			}

			@Override
			public Term pc(final int idx) {
				return require(sv.pc(idx), "pc");
			}

			@Override
			public Term aux(final int id, final TermVariable auxVar, final int idx) {
				return require(sv.aux(id, auxVar, idx), auxVar);
			}

			private Term require(final Term constant, final Object name) {
				if (constant == null) {
					throw new IllegalStateException("The query declared no constant for " + name);
				}
				return constant;
			}
		};
	}

	/** The pc value of each head of each loop. */
	public Map<STATE, Integer> getHeadNodes() {
		return Collections.unmodifiableMap(mHeadNodes);
	}

	/** The non-old program variables that occur in some edge. */
	public Set<IProgramVar> getVars() {
		return Collections.unmodifiableSet(mVars);
	}

	/** The old variables that occur in some edge. They are not part of the state, see the class javadoc. */
	public Set<IProgramVar> getOldVars() {
		return Collections.unmodifiableSet(mOldVars);
	}

	/** The pc value of each "waypoint", a state outside a loop that a break out of the loop can jump to. */
	public Map<STATE, Integer> getWaypointNodes() {
		return Collections.unmodifiableMap(mWaypointNodes);
	}

	/** The automaton states a letter path of a step from the pc value {@code pc} can start in. */
	public Set<STATE> getSourceStates(final int pc) {
		return Collections.unmodifiableSet(mSourceStates.getOrDefault(pc, Collections.emptySet()));
	}

	/** The automaton states a letter path of a step into the pc value {@code pc} can end in. */
	public Set<STATE> getTargetStates(final int pc) {
		return Collections.unmodifiableSet(mTargetStates.getOrDefault(pc, Collections.emptySet()));
	}

	/** Every pair of pc values with a step from the first to the second, without the stutter of {@link #FINAL}. */
	public Set<List<Integer>> getStepPairs() {
		final Map<DagNode, Set<Integer>> targets = new HashMap<>();
		for (int position = mDagNodes.size() - 1; position >= 0; position--) {
			final DagNode node = mDagNodes.get(position);
			final Set<Integer> here = new HashSet<>(node.mTargetPcs);
			for (final DagEdge edge : node.mOutgoing) {
				here.addAll(targets.get(edge.mTarget));
			}
			targets.put(node, here);
		}
		final Set<List<Integer>> result = new LinkedHashSet<>();
		for (final DagNode source : mSources) {
			for (final int target : targets.get(source)) {
				result.add(List.of(source.mSourcePc, target));
			}
		}
		return result;
	}

	public int getNumNodes() {
		return mNumNodes;
	}

	/** The number of edges with a formula. */
	public int getNumEdges() {
		return mFormulas.size();
	}

	/** The sort of the pc. */
	public CounterSort getCounterSort() {
		return mCounterSort;
	}

	/** The term for the pc value {@code node}. */
	public Term pcValue(final Script script, final int node) {
		return mCounterSort.value(script, node);
	}

	/**
	 * The relation between step {@code idx} and step {@code idx + 1}: some path is taken, i.e. pc and variables of the two
	 * steps fit to it, and every variable the path does not assign keeps its value.
	 * <p>
	 * For constants only: over term variables every shared subformula would hold its free variables, which is the number
	 * of nodes times the number of variables. See {@link #composeSteps} for that.
	 */
	public Term step(final int idx, final StepVars sv, final ManagedScript mgdScript) {
		if (mFullFrameEncoding == null) {
			mFullFrameEncoding = new EncodingBuilder().build(true);
		}
		final Script script = mgdScript.getScript();
		return or(script, List.of(encode(mFullFrameEncoding, idx, sv, mgdScript, pc -> true, pc -> true),
				stutter(idx, sv, script)));
	}

	/** The self loop of {@link #FINAL}. */
	private Term stutter(final int idx, final StepVars sv, final Script script) {
		final List<Term> conjuncts = new ArrayList<>();
		conjuncts.add(SmtUtils.binaryEquality(script, sv.pc(idx), pcValue(script, FINAL)));
		conjuncts.add(SmtUtils.binaryEquality(script, sv.pc(idx + 1), pcValue(script, FINAL)));
		for (final IProgramVar pv : mVars) {
			conjuncts.add(SmtUtils.binaryEquality(script, sv.var(pv, idx + 1), sv.var(pv, idx)));
		}
		return and(script, conjuncts);
	}

	/**
	 * The relation between step {@code idx} and step {@code idx + 1} on a run that reaches {@link #FINAL} exactly at its
	 * end: only the paths of this kind, and never the stutter. A path from {@link #INIT} can only be a run's first, since
	 * INIT has no incoming path, and a path into FINAL only its last. A variable that nothing reads any more is left
	 * unconstrained, see the class javadoc.
	 *
	 * @param fromInit
	 *            whether these are the paths that leave INIT or those that do not
	 * @param intoFinal
	 *            whether these are the paths that enter FINAL or those that do not
	 */
	public Term step(final int idx, final StepVars sv, final ManagedScript mgdScript, final boolean fromInit,
			final boolean intoFinal) {
		return encode(queryEncoding(), idx, sv, mgdScript, pc -> (pc == INIT) == fromInit,
				pc -> (pc == FINAL) == intoFinal);
	}

	private Encoding queryEncoding() {
		if (mQueryEncoding == null) {
			mQueryEncoding = new EncodingBuilder().build(false);
		}
		return mQueryEncoding;
	}

	private Term encode(final Encoding encoding, final int idx, final StepVars sv, final ManagedScript mgdScript,
			final IntPredicate fromPc, final IntPredicate toPc) {
		final Script script = mgdScript.getScript();
		final Term falseTerm = script.term("false");

		final Map<DagNode, Term> atSource = new LinkedHashMap<>();
		final boolean[] reached = new boolean[mDagNodes.size()];
		final Deque<DagNode> worklist = new ArrayDeque<>();
		for (final DagNode source : mSources) {
			if (!fromPc.test(source.mSourcePc)) {
				continue;
			}
			final Term isSource = SmtUtils.binaryEquality(script, sv.pc(idx), pcValue(script, source.mSourcePc));
			if (isSource != falseTerm) {
				atSource.put(source, isSource);
				reached[source.mPosition] = true;
				worklist.add(source);
			}
		}
		while (!worklist.isEmpty()) {
			for (final DagEdge edge : worklist.poll().mOutgoing) {
				if (!reached[edge.mTarget.mPosition]) {
					reached[edge.mTarget.mPosition] = true;
					worklist.add(edge.mTarget);
				}
			}
		}

		final Map<Integer, Term> isTarget = new HashMap<>();
		final Term[] formulas = new Term[mDagNodes.size()];
		for (int position = mDagNodes.size() - 1; position >= 0; position--) {
			if (!reached[position]) {
				continue;
			}
			final DagNode node = mDagNodes.get(position);
			final List<Term> disjuncts = new ArrayList<>();
			for (final TargetCode target : encoding.targetCode().getOrDefault(node, Collections.emptyList())) {
				if (!toPc.test(target.pc())) {
					continue;
				}
				final Term isPc = isTarget.computeIfAbsent(target.pc(),
						pc -> SmtUtils.binaryEquality(script, sv.pc(idx + 1), pcValue(script, pc)));
				if (isPc == falseTerm) {
					continue;
				}
				final List<Term> conjuncts = new ArrayList<>();
				conjuncts.add(isPc);
				for (final Version output : target.outputs()) {
					conjuncts.add(
							SmtUtils.binaryEquality(script, sv.var(output.var(), idx + 1), termOf(output, sv, idx)));
				}
				disjuncts.add(and(script, conjuncts));
			}
			for (final DagEdge edge : node.mOutgoing) {
				final Term behind = formulas[edge.mTarget.mPosition];
				if (behind == falseTerm) {
					continue;
				}
				final EdgeCode code = encoding.edgeCode().get(edge);
				final List<Term> conjuncts = new ArrayList<>();
				if (edge.mFormulaIndex >= 0) {
					conjuncts.add(instantiate(edge, code, idx, sv, mgdScript));
				}
				for (final Join join : code.joins()) {
					conjuncts.add(SmtUtils.binaryEquality(script, termOf(join.atNode(), sv, idx),
							termOf(join.onEdge(), sv, idx)));
				}
				conjuncts.add(behind);
				disjuncts.add(and(script, conjuncts));
			}
			formulas[position] = or(script, disjuncts);
		}

		final List<Term> disjuncts = new ArrayList<>();
		for (final Map.Entry<DagNode, Term> source : atSource.entrySet()) {
			disjuncts.add(and(script, List.of(source.getValue(), formulas[source.getKey().mPosition])));
		}
		return or(script, disjuncts);
	}

	/**
	 * The relation of {@link #step(int, StepVars, ManagedScript)} with the paths of a step composed, so that it has no
	 * variables inside but the auxiliary ones of the composition, which is what quantifier elimination can handle. This
	 * costs what a query must not pay for: its size is the sum over all pairs of pc values of their paths.
	 * <p>
	 * Must be called when the script is not locked, since composing takes the lock. The relation it returns need not.
	 *
	 * @return the relation of one step, as a function of the step's index and variables
	 */
	public BiFunction<Integer, StepVars, Term> composeSteps(final IUltimateServiceProvider services,
			final ILogger logger, final ManagedScript mgdScript) {
		final UnmodifiableTransFormula empty = TransFormulaBuilder.getTrivialTransFormula(mgdScript);
		final Map<DagNode, List<Pair<UnmodifiableTransFormula, DagNode>>> edges = new LinkedHashMap<>();
		final Map<Integer, List<DagNode>> nodesOfTarget = new LinkedHashMap<>();
		for (final DagNode node : mDagNodes) {
			final List<Pair<UnmodifiableTransFormula, DagNode>> outgoing = new ArrayList<>();
			for (final DagEdge edge : node.mOutgoing) {
				outgoing.add(new Pair<>(edge.mFormulaIndex < 0 ? empty : mFormulas.get(edge.mFormulaIndex), edge.mTarget));
			}
			edges.put(node, outgoing);
			for (final int pc : node.mTargetPcs) {
				nodesOfTarget.computeIfAbsent(pc, k -> new ArrayList<>()).add(node);
			}
		}
		final PathFormulaComposer<DagNode> composer = new PathFormulaComposer<>(services, logger, mgdScript, edges);
		final List<ComposedStep> steps = new ArrayList<>();
		for (final DagNode source : mSources) {
			for (final Map.Entry<Integer, List<DagNode>> target : nodesOfTarget.entrySet()) {
				final List<UnmodifiableTransFormula> alternatives = new ArrayList<>();
				for (final DagNode node : target.getValue()) {
					final UnmodifiableTransFormula paths = composer.pathsBetween(source, node);
					if (paths != null) {
						alternatives.add(paths);
					}
				}
				final UnmodifiableTransFormula formula =
						LoopTreeFormulaBuilder.combineAlternatives(logger, services, mgdScript, alternatives);
				if (formula != null) {
					steps.add(new ComposedStep(source.mSourcePc, target.getKey(), formula));
				}
			}
		}
		return (idx, sv) -> composedStep(steps, idx, sv, mgdScript);
	}

	private Term composedStep(final List<ComposedStep> steps, final int idx, final StepVars sv,
			final ManagedScript mgdScript) {
		final Script script = mgdScript.getScript();
		final List<Term> disjuncts = new ArrayList<>();
		for (int id = 0; id < steps.size(); id++) {
			final UnmodifiableTransFormula tf = steps.get(id).formula();
			final Term isSource = SmtUtils.binaryEquality(script, sv.pc(idx), pcValue(script, steps.get(id).from()));
			final Term isTarget = SmtUtils.binaryEquality(script, sv.pc(idx + 1), pcValue(script, steps.get(id).to()));
			if (SmtUtils.isFalseLiteral(isSource) || SmtUtils.isFalseLiteral(isTarget)) {
				continue;
			}
			final Map<Term, Term> substitution = new HashMap<>();
			final Set<IProgramVar> assigned = assignedVars(tf);
			for (final Map.Entry<IProgramVar, TermVariable> in : tf.getInVars().entrySet()) {
				final IProgramVar pv = in.getKey();
				substitution.put(in.getValue(), pv.isOldvar() ? pv.getDefaultConstant() : sv.var(pv, idx));
			}
			for (final IProgramVar pv : assigned) {
				final TermVariable out = tf.getOutVars().get(pv);
				if (out != null) {
					substitution.put(out, sv.var(pv, idx + 1));
				}
			}
			for (final TermVariable aux : tf.getAuxVars()) {
				substitution.put(aux, sv.aux(id, aux, idx));
			}
			final List<Term> conjuncts = new ArrayList<>();
			conjuncts.add(isSource);
			conjuncts.add(isTarget);
			conjuncts.add(PureSubstitution.apply(mgdScript, substitution,
					IteComparisonEncoder.apply(script, tf.getFormula())));
			for (final IProgramVar pv : mVars) {
				if (!assigned.contains(pv)) {
					conjuncts.add(SmtUtils.binaryEquality(script, sv.var(pv, idx + 1), sv.var(pv, idx)));
				}
			}
			disjuncts.add(SmtUtils.and(script, conjuncts));
		}
		disjuncts.add(stutter(idx, sv, script));
		return SmtUtils.or(script, disjuncts);
	}

	/** A conjunction that keeps its conjuncts as they are, see the class javadoc. */
	private static Term and(final Script script, final List<Term> conjuncts) {
		return junction(script, "and", "true", "false", conjuncts);
	}

	/** A disjunction that keeps its disjuncts as they are, see the class javadoc. */
	private static Term or(final Script script, final List<Term> disjuncts) {
		return junction(script, "or", "false", "true", disjuncts);
	}

	private static Term junction(final Script script, final String connective, final String neutral,
			final String absorbing, final List<Term> juncts) {
		final Term neutralTerm = script.term(neutral);
		final Term absorbingTerm = script.term(absorbing);
		final Set<Term> distinct = new LinkedHashSet<>();
		for (final Term junct : juncts) {
			if (junct == absorbingTerm) {
				return absorbingTerm;
			}
			if (junct != neutralTerm) {
				distinct.add(junct);
			}
		}
		if (distinct.isEmpty()) {
			return neutralTerm;
		}
		if (distinct.size() == 1) {
			return distinct.iterator().next();
		}
		return script.term(connective, distinct.toArray(new Term[0]));
	}

	private Term termOf(final Version version, final StepVars sv, final int idx) {
		final IProgramVar pv = version.var();
		if (version.owner() == STEP_START) {
			return pv.isOldvar() ? pv.getDefaultConstant() : sv.var(pv, idx);
		}
		return sv.aux(version.owner(), pv.getTermVariable(), idx);
	}

	private Term instantiate(final DagEdge edge, final EdgeCode code, final int idx, final StepVars sv,
			final ManagedScript mgdScript) {
		final UnmodifiableTransFormula tf = mFormulas.get(edge.mFormulaIndex);
		final Map<Term, Term> substitution = new HashMap<>();
		for (final Map.Entry<TermVariable, Version> version : code.versions().entrySet()) {
			substitution.put(version.getKey(), termOf(version.getValue(), sv, idx));
		}
		for (final TermVariable aux : tf.getAuxVars()) {
			substitution.put(aux, sv.aux(edge.mId, aux, idx));
		}
		final Term encoded = mEncodedFormulas.computeIfAbsent(edge.mFormulaIndex,
				index -> IteComparisonEncoder.apply(mgdScript.getScript(), tf.getFormula()));
		return PureSubstitution.apply(mgdScript, substitution, encoded);
	}

	/** The number of nodes of the DAG of {@code term}, shared subterms counted once. */
	public static long dagSize(final Term term) {
		return Long.parseLong(new DagSizePrinter(term).toString());
	}

	/**
	 * What one unrolled step costs, for the log: the frame equalities and auxiliary variables a query's step has, and the
	 * size of the edges' formulas, each counted on its own.
	 */
	public String getStatistics() {
		long auxVars = 0;
		long formulaDagSize = 0;
		for (final UnmodifiableTransFormula tf : mFormulas) {
			auxVars += tf.getAuxVars().size();
			formulaDagSize += dagSize(tf.getFormula());
		}
		return mFormulas.size() + " edge(s), " + mVars.size() + " variable(s), "
				+ queryEncoding().numberOfFrameEqualities() + " frame equalities and " + auxVars
				+ " aux variable(s) per step, edge formulas of DAG size " + formulaDagSize;
	}
}
