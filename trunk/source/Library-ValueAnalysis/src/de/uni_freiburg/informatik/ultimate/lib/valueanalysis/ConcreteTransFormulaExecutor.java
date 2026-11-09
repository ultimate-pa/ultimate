/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE ValueAnalysis Library.
 *
 * The ULTIMATE ValueAnalysis Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ValueAnalysis Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ValueAnalysis Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ValueAnalysis Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ValueAnalysis Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.valueanalysis;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.IConcreteValue.ArrayValue;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.IConcreteValue.BitvectorValue;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.IConcreteValue.BoolValue;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.IConcreteValue.NumberValue;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;

/**
 * Executes an {@link UnmodifiableTransFormula} on a concrete valuation, without a solver.
 * <p>
 * The in-variables take their values from the valuation before the step. The values of the other variables of the
 * formula (out-variables that the step assigns, auxiliary variables, and in-variables that were never assigned) are
 * found as follows:
 * <ul>
 * <li>a top-level conjunct {@code (= s t)} in which {@code v} occurs exactly once, in {@code s}, defines {@code v} as
 * soon as all other variables have values and the operations around {@code v} can be inverted (e.g.
 * {@code (= (+ v 1) n)} gives {@code v = n - 1}), repeated until nothing changes;</li>
 * <li>an array variable whose cells a conjunct fixes, {@code (= (select a i) t)}, is tried with those cells
 * first;</li>
 * <li>whatever is still open is chosen, variable by variable - first the variables the pool has
 * {@linkplain NondeterminismPool#preferred preferred} values for, and these first among them - then among the
 * literals of the conjuncts the variable occurs in (and their neighbours), then from the
 * {@link NondeterminismPool};</li>
 * <li>after each choice, every conjunct whose variables all have values is checked, and a choice that falsifies one
 * is abandoned.</li>
 * </ul>
 * Each complete assignment is finally checked against the <em>whole</em> formula, and only those that satisfy it
 * become successors. Every successor is therefore a real execution of the step: the analysis under-approximates.
 * Steps it cannot evaluate yield no successor, which keeps it so.
 * <p>
 * An out-variable the formula does not mention at all (a plain havoc) gets no value: it is left unassigned, and its
 * first read chooses one. This keeps a step that havocs many variables from multiplying the choices.
 * <p>
 * A formula that is a disjunction, as large block encoding produces them, is handled one disjunct at a time, so that
 * each disjunct's equalities can define its variables.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class ConcreteTransFormulaExecutor {

	/**
	 * How a step treats variables in a way that differs between internal, call and return steps.
	 */
	public enum StepKind {
		/**
		 * An internal step: a variable that is an in-variable but not an out-variable is havoced.
		 */
		INTERNAL,
		/**
		 * A call or a return. Their formulas only say how the variables they mention are passed between caller and
		 * callee; restoring and havocing the rest is up to the caller of this class.
		 */
		CALL_OR_RETURN
	}

	/**
	 * How many partial assignments the search of one step may visit per successor it may yield. Bounds the work spent
	 * on choices that the formula rejects.
	 */
	private static final int NODES_PER_SUCCESSOR = 64;

	private final NondeterminismPool mPool;
	private final int mMaxSuccessors;
	private final Map<UnmodifiableTransFormula, Plan> mPlans = new IdentityHashMap<>();

	private long mSteps;
	private long mUnsupportedSteps;
	private long mTruncatedSteps;

	/**
	 * @param pool
	 *            the values to choose from for variables a step leaves open
	 * @param maxSuccessors
	 *            how many successors one step yields at most
	 */
	public ConcreteTransFormulaExecutor(final NondeterminismPool pool, final int maxSuccessors) {
		mPool = pool;
		mMaxSuccessors = maxSuccessors;
	}

	/**
	 * @param tf
	 *            the step
	 * @param pre
	 *            the valuation the step reads its in-variables and program constants from
	 * @param base
	 *            the valuation the step writes its out-variables into; the same as {@code pre} for an internal step
	 * @param kind
	 *            the kind of the step
	 * @return the distinct valuations after the step, possibly none
	 */
	public List<Map<IProgramVarOrConst, IConcreteValue>> execute(final UnmodifiableTransFormula tf,
			final Map<IProgramVarOrConst, IConcreteValue> pre, final Map<IProgramVarOrConst, IConcreteValue> base,
			final StepKind kind) {
		final Set<Map<IProgramVarOrConst, IConcreteValue>> valuations = new LinkedHashSet<>();
		for (final Successor successor : executeDetailed(tf, pre, base, kind).successors()) {
			valuations.add(successor.valuation());
		}
		return new ArrayList<>(valuations);
	}

	/**
	 * One execution of a step.
	 *
	 * @param valuation
	 *            the valuation after the step
	 * @param chosenReads
	 *            the value this execution chose for every in-variable the valuation before the step had none for
	 */
	public record Successor(Map<IProgramVarOrConst, IConcreteValue> valuation,
			Map<IProgramVar, IConcreteValue> chosenReads) {
	}

	/**
	 * The successors of a step, and whether they are all of them.
	 *
	 * @param successors
	 *            the distinct executions of the step, each a real one
	 * @param exhaustive
	 *            whether {@code successors} are exactly the executions of the step: no value had to be chosen, and
	 *            nothing was unsupported or cut off. Only then does an empty list mean that the step cannot be taken.
	 */
	public record Execution(List<Successor> successors, boolean exhaustive) {
	}

	/**
	 * {@link #execute}, together with whether its successors are all there are.
	 */
	public Execution executeDetailed(final UnmodifiableTransFormula tf,
			final Map<IProgramVarOrConst, IConcreteValue> pre, final Map<IProgramVarOrConst, IConcreteValue> base,
			final StepKind kind) {
		mSteps++;
		final Plan plan = mPlans.computeIfAbsent(tf, Plan::new);
		final Map<TermVariable, IConcreteValue> env = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			final IConcreteValue value = pre.get(entry.getKey());
			if (value != null) {
				env.put(entry.getValue(), value);
			}
		}
		final Set<Successor> results = new LinkedHashSet<>();
		final Search search = new Search(plan);
		try {
			final Map<IProgramVarOrConst, IConcreteValue> chosenConstants = new HashMap<>();
			for (final IProgramConst constant : plan.mConstants) {
				IConcreteValue value = pre.get(constant);
				if (value == null) {
					// A program constant that was never read: it is the same in the whole execution, so a single
					// choice is fixed here and kept in the valuation.
					value = mPool.candidates(constant.getSort()).get(0);
					chosenConstants.put(constant, value);
					search.mChose = true;
				}
				search.mConstants.put(constant.getDefaultConstant().getFunction().getName(), value);
			}
			final Consumer<Map<TermVariable, IConcreteValue>> sink =
					assignment -> results.add(new Successor(post(tf, assignment, base, chosenConstants, kind),
							chosenReads(tf, assignment, pre)));
			for (final Branch branch : plan.mBranches) {
				search.solve(branch, env, sink);
			}
		} catch (final UnsupportedTermException e) {
			search.mUnsupported = true;
		}
		if (search.mUnsupported) {
			mUnsupportedSteps++;
		}
		if (search.mTruncated) {
			mTruncatedSteps++;
		}
		return new Execution(new ArrayList<>(results),
				!search.mUnsupported && !search.mTruncated && !search.mChose);
	}

	private static Map<IProgramVar, IConcreteValue> chosenReads(final UnmodifiableTransFormula tf,
			final Map<TermVariable, IConcreteValue> assignment, final Map<IProgramVarOrConst, IConcreteValue> pre) {
		final Map<IProgramVar, IConcreteValue> result = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			if (!pre.containsKey(entry.getKey())) {
				final IConcreteValue value = assignment.get(entry.getValue());
				if (value != null) {
					result.put(entry.getKey(), value);
				}
			}
		}
		return result;
	}

	private static Map<IProgramVarOrConst, IConcreteValue> post(final UnmodifiableTransFormula tf,
			final Map<TermVariable, IConcreteValue> assignment, final Map<IProgramVarOrConst, IConcreteValue> base,
			final Map<IProgramVarOrConst, IConcreteValue> chosenConstants, final StepKind kind) {
		final Map<IProgramVarOrConst, IConcreteValue> result = new HashMap<>(base);
		result.putAll(chosenConstants);
		if (kind == StepKind.INTERNAL) {
			for (final IProgramVar pv : tf.getInVars().keySet()) {
				if (!tf.getOutVars().containsKey(pv)) {
					// Havoced: its value afterwards is open again, a later read chooses one.
					result.remove(pv);
				}
			}
		}
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			final IConcreteValue value = assignment.get(entry.getValue());
			if (value != null) {
				result.put(entry.getKey(), value);
			} else if (entry.getValue() != tf.getInVars().get(entry.getKey())) {
				// A havoc the formula does not constrain: unassigned, a later read chooses a value.
				result.remove(entry.getKey());
			}
			// Otherwise the step neither reads nor changes a variable that was never assigned.
		}
		return result;
	}

	/**
	 * @return how many steps were executed
	 */
	public long getSteps() {
		return mSteps;
	}

	/**
	 * @return how many steps lost successors because some part of them could not be evaluated
	 */
	public long getUnsupportedSteps() {
		return mUnsupportedSteps;
	}

	/**
	 * @return how many steps lost successors to the limit on successors or on the search for them
	 */
	public long getTruncatedSteps() {
		return mTruncatedSteps;
	}

	/**
	 * The search for complete assignments of one step.
	 */
	private final class Search {
		private final Plan mPlan;
		private final Map<String, IConcreteValue> mConstants = new HashMap<>();
		private int mSuccessorBudget = mMaxSuccessors;
		private long mNodeBudget = (long) mMaxSuccessors * NODES_PER_SUCCESSOR;
		private boolean mUnsupported;
		private boolean mTruncated;
		// Whether some value was chosen rather than computed, so that the successors need not be all there are
		private boolean mChose;

		Search(final Plan plan) {
			mPlan = plan;
		}

		void solve(final Branch branch, final Map<TermVariable, IConcreteValue> partial,
				final Consumer<Map<TermVariable, IConcreteValue>> sink) {
			if (mSuccessorBudget <= 0 || mNodeBudget <= 0) {
				mTruncated = true;
				return;
			}
			mNodeBudget--;
			final Map<TermVariable, IConcreteValue> env = new HashMap<>(partial);
			propagate(branch, env);
			if (violatesBoundConjunct(branch, env)) {
				return;
			}
			final TermVariable open = pickOpen(branch, env);
			if (open == null) {
				try {
					if (GroundTermEvaluator.evaluateBoolean(branch.mFormula, env, mConstants)) {
						mSuccessorBudget--;
						sink.accept(env);
					}
				} catch (final UnsupportedTermException e) {
					mUnsupported = true;
				}
				return;
			}
			mChose = true;
			for (final IConcreteValue value : candidates(branch, open, env)) {
				if (mSuccessorBudget <= 0 || mNodeBudget <= 0) {
					mTruncated = true;
					return;
				}
				env.put(open, value);
				solve(branch, env, sink);
			}
		}

		private List<IConcreteValue> candidates(final Branch branch, final TermVariable open,
				final Map<TermVariable, IConcreteValue> env) {
			final List<IConcreteValue> pool = mPool.candidates(open.getSort());
			final List<IConcreteValue> preferred = mPool.preferred(mPlan.mProgramVars.get(open), open.getSort());
			final List<ArrayFact> facts = branch.mArrayFacts.get(open);
			final List<IConcreteValue> harvested = branch.mHarvested.get(open);
			if (facts == null && harvested == null && preferred.isEmpty()) {
				return pool;
			}
			final Set<IConcreteValue> result = new LinkedHashSet<>();
			if (facts != null) {
				result.add(arrayFromFacts(pool.get(0), facts, env));
			}
			result.addAll(preferred);
			if (harvested != null) {
				result.addAll(harvested);
			}
			result.addAll(pool);
			return new ArrayList<>(result);
		}

		/**
		 * @return {@code base} with every fact {@code (select ... (select a i1) ... in) = v} stored whose indices and
		 *         value can already be evaluated, e.g. the memory cells an initialization writes
		 */
		private IConcreteValue arrayFromFacts(final IConcreteValue base, final List<ArrayFact> facts,
				final Map<TermVariable, IConcreteValue> env) {
			IConcreteValue result = base;
			for (final ArrayFact fact : facts) {
				try {
					final List<IConcreteValue> indices = new ArrayList<>(fact.mIndices.size());
					for (final Term index : fact.mIndices) {
						indices.add(GroundTermEvaluator.evaluate(index, env, mConstants));
					}
					result = storeNested(result, indices, 0,
							GroundTermEvaluator.evaluate(fact.mValue, env, mConstants));
				} catch (final UnsupportedTermException e) {
					// Not evaluable yet, or not an array where the fact needs one: the fact is left out, the check of
					// the whole formula decides.
				}
			}
			return result;
		}

		private IConcreteValue storeNested(final IConcreteValue array, final List<IConcreteValue> indices,
				final int position, final IConcreteValue value) {
			if (!(array instanceof final ArrayValue arrayValue)) {
				throw new UnsupportedTermException("not an array");
			}
			final IConcreteValue index = indices.get(position);
			if (position == indices.size() - 1) {
				return arrayValue.store(index, value);
			}
			return arrayValue.store(index, storeNested(arrayValue.select(index), indices, position + 1, value));
		}

		private void propagate(final Branch branch, final Map<TermVariable, IConcreteValue> env) {
			boolean changed = true;
			while (changed) {
				changed = false;
				for (final Definition definition : branch.mDefinitions) {
					if (env.containsKey(definition.mTarget)) {
						continue;
					}
					if (definition.mValue != null) {
						env.put(definition.mTarget, definition.mValue);
						changed = true;
						continue;
					}
					if (!env.keySet().containsAll(definition.mRhsVars)) {
						continue;
					}
					try {
						final IConcreteValue rhs = GroundTermEvaluator.evaluate(definition.mRhs, env, mConstants);
						env.put(definition.mTarget, GroundTermEvaluator.solveFor(definition.mLhs, definition.mTarget,
								rhs, env, mConstants));
						changed = true;
					} catch (final UnsupportedTermException e) {
						// Another definition or a choice may still give the variable a value.
					}
				}
			}
		}

		/**
		 * @return whether a conjunct all of whose variables have values is false
		 */
		private boolean violatesBoundConjunct(final Branch branch, final Map<TermVariable, IConcreteValue> env) {
			for (final Conjunct conjunct : branch.mConjuncts) {
				if (!env.keySet().containsAll(conjunct.mVars)) {
					continue;
				}
				try {
					if (!GroundTermEvaluator.evaluateBoolean(conjunct.mTerm, env, mConstants)) {
						return true;
					}
				} catch (final UnsupportedTermException e) {
					// The check of the whole formula will tell.
				}
			}
			return false;
		}

		/**
		 * @return an open variable of the conjunct with the fewest open variables, so that a choice is checked as
		 *         early as possible; null if every variable of the branch has a value
		 */
		private TermVariable pickOpen(final Branch branch, final Map<TermVariable, IConcreteValue> env) {
			// A variable the pool knows preferred values for comes first: whatever it is defined by (typically an
			// auxiliary variable, e.g. the result of a nondeterministic call) can then be solved for instead of
			// guessed.
			for (final Conjunct conjunct : branch.mConjuncts) {
				for (final TermVariable tv : conjunct.mVars) {
					if (!env.containsKey(tv)
							&& !mPool.preferred(mPlan.mProgramVars.get(tv), tv.getSort()).isEmpty()) {
						return tv;
					}
				}
			}
			TermVariable best = null;
			int fewestOpen = Integer.MAX_VALUE;
			for (final Conjunct conjunct : branch.mConjuncts) {
				int open = 0;
				TermVariable first = null;
				for (final TermVariable tv : conjunct.mVars) {
					if (!env.containsKey(tv)) {
						open++;
						if (first == null) {
							first = tv;
						}
					}
				}
				if (open > 0 && open < fewestOpen) {
					fewestOpen = open;
					best = first;
				}
			}
			return best;
		}
	}

	/**
	 * What is computed once per formula: its disjuncts, and its program constants.
	 */
	private static final class Plan {
		private final List<Branch> mBranches = new ArrayList<>();
		private final List<IProgramConst> mConstants;
		// The program variable behind each in- and out-variable, for NondeterminismPool#preferred
		private final Map<TermVariable, IProgramVar> mProgramVars = new HashMap<>();

		Plan(final UnmodifiableTransFormula tf) {
			for (final Term disjunct : SmtUtils.getDisjuncts(tf.getFormula())) {
				mBranches.add(new Branch(disjunct));
			}
			mConstants = List.copyOf(tf.getNonTheoryConsts());
			for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
				mProgramVars.put(entry.getValue(), entry.getKey());
			}
			for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
				mProgramVars.put(entry.getValue(), entry.getKey());
			}
		}
	}

	/**
	 * A disjunct of a formula: its top-level conjuncts, the equalities among them that define a variable, and the
	 * literals that occur together with each variable.
	 */
	private static final class Branch {
		private final Term mFormula;
		private final List<Conjunct> mConjuncts = new ArrayList<>();
		private final List<Definition> mDefinitions = new ArrayList<>();
		private final Map<TermVariable, List<ArrayFact>> mArrayFacts = new HashMap<>();
		private final Map<TermVariable, List<IConcreteValue>> mHarvested = new HashMap<>();

		Branch(final Term formula) {
			mFormula = formula;
			for (final Term conjunct : SmtUtils.getConjuncts(formula)) {
				final Conjunct c = new Conjunct(conjunct);
				mConjuncts.add(c);
				addDefinitions(conjunct);
				harvest(c);
			}
		}

		private void addDefinitions(final Term conjunct) {
			if (conjunct instanceof final TermVariable tv) {
				mDefinitions.add(new Definition(tv, BoolValue.TRUE));
				return;
			}
			if (!(conjunct instanceof final ApplicationTerm app)) {
				return;
			}
			final Term[] params = app.getParameters();
			final String name = app.getFunction().getName();
			if ("not".equals(name) && params[0] instanceof final TermVariable tv) {
				mDefinitions.add(new Definition(tv, BoolValue.FALSE));
			} else if ("=".equals(name) && params.length == 2) {
				addEquality(params[0], params[1]);
				addEquality(params[1], params[0]);
				addArrayFact(params[0], params[1]);
				addArrayFact(params[1], params[0]);
			}
		}

		/**
		 * Remembers {@code lhs = rhs} if {@code lhs} is a select chain {@code (select ... (select a i1) ... in)} on an
		 * array variable {@code a} that occurs neither in the indices nor in {@code rhs}.
		 */
		private void addArrayFact(final Term lhs, final Term rhs) {
			final List<Term> indices = new ArrayList<>();
			Term current = lhs;
			while (current instanceof final ApplicationTerm app && "select".equals(app.getFunction().getName())) {
				indices.add(0, app.getParameters()[1]);
				current = app.getParameters()[0];
			}
			if (indices.isEmpty() || !(current instanceof final TermVariable array)) {
				return;
			}
			if (Arrays.asList(rhs.getFreeVars()).contains(array)) {
				return;
			}
			for (final Term index : indices) {
				if (Arrays.asList(index.getFreeVars()).contains(array)) {
					return;
				}
			}
			mArrayFacts.computeIfAbsent(array, x -> new ArrayList<>()).add(new ArrayFact(indices, rhs));
		}

		/**
		 * Adds a definition of each variable that occurs exactly once in {@code lhs} and not in {@code rhs}; whether
		 * the operations around it can be inverted only shows when the definition is used.
		 */
		private void addEquality(final Term lhs, final Term rhs) {
			final List<TermVariable> rhsVars = Arrays.asList(rhs.getFreeVars());
			for (final TermVariable tv : lhs.getFreeVars()) {
				if (!rhsVars.contains(tv) && occurrences(lhs, tv, 2) == 1) {
					mDefinitions.add(new Definition(tv, lhs, rhs));
				}
			}
		}

		/**
		 * @return how often {@code tv} occurs in {@code term}, counting only up to {@code limit}
		 */
		private static int occurrences(final Term term, final TermVariable tv, final int limit) {
			if (term == tv) {
				return 1;
			}
			if (!Arrays.asList(term.getFreeVars()).contains(tv)) {
				return 0;
			}
			if (term instanceof final AnnotatedTerm annotated) {
				return occurrences(annotated.getSubterm(), tv, limit);
			}
			if (!(term instanceof final ApplicationTerm app)) {
				// Bound by a let or a quantifier: not something to invert.
				return limit;
			}
			int count = 0;
			for (final Term param : app.getParameters()) {
				count += occurrences(param, tv, limit - count);
				if (count >= limit) {
					return limit;
				}
			}
			return count;
		}

		/**
		 * Remembers for each variable of {@code conjunct} the literals of its sort that occur in it, and for numbers
		 * their neighbours: the values a comparison with a literal most likely needs.
		 */
		private void harvest(final Conjunct conjunct) {
			if (conjunct.mVars.isEmpty()) {
				return;
			}
			final Map<Sort, Set<IConcreteValue>> literals = new HashMap<>();
			for (final Term literal : literals(conjunct.mTerm)) {
				final IConcreteValue value;
				try {
					value = GroundTermEvaluator.evaluate(literal, Collections.emptyMap(), Collections.emptyMap());
				} catch (final UnsupportedTermException e) {
					continue;
				}
				final Set<IConcreteValue> values = literals.computeIfAbsent(literal.getSort(), x -> new LinkedHashSet<>());
				values.add(value);
				values.addAll(neighbours(value));
			}
			for (final TermVariable tv : conjunct.mVars) {
				final Set<IConcreteValue> values = literals.get(tv.getSort());
				if (values == null) {
					continue;
				}
				final List<IConcreteValue> harvested = mHarvested.computeIfAbsent(tv, x -> new ArrayList<>());
				for (final IConcreteValue value : values) {
					if (!harvested.contains(value)) {
						harvested.add(value);
					}
				}
			}
		}

		private static List<IConcreteValue> neighbours(final IConcreteValue value) {
			if (value instanceof final NumberValue number) {
				return List.of(new NumberValue(number.value().add(Rational.ONE)),
						new NumberValue(number.value().sub(Rational.ONE)));
			}
			if (value instanceof final BitvectorValue bitvector) {
				final BitvectorConstant one =
						new BitvectorConstant(BigInteger.ONE, bitvector.value().getIndex());
				return List.of(new BitvectorValue(BitvectorConstant.bvadd(bitvector.value(), one)),
						new BitvectorValue(BitvectorConstant.bvsub(bitvector.value(), one)));
			}
			return List.of();
		}

		/**
		 * @return the numeric and bitvector literals of {@code term}
		 */
		private static List<Term> literals(final Term term) {
			final List<Term> result = new ArrayList<>();
			final Set<Term> visited = Collections.newSetFromMap(new IdentityHashMap<>());
			final Deque<Term> todo = new ArrayDeque<>();
			todo.push(term);
			while (!todo.isEmpty()) {
				final Term current = todo.pop();
				if (!visited.add(current)) {
					continue;
				}
				if (current instanceof ConstantTerm) {
					result.add(current);
				} else if (current instanceof final ApplicationTerm app) {
					if (BitvectorUtils.isBitvectorConstant(app.getFunction())) {
						result.add(app);
					} else {
						for (final Term param : app.getParameters()) {
							todo.push(param);
						}
					}
				} else if (current instanceof final AnnotatedTerm annotated) {
					todo.push(annotated.getSubterm());
				} else if (current instanceof final LetTerm let) {
					todo.push(let.getSubTerm());
					for (final Term value : let.getValues()) {
						todo.push(value);
					}
				}
			}
			return result;
		}
	}

	/**
	 * A top-level conjunct of a branch and its free variables, in a fixed order so that the search is deterministic.
	 */
	private static final class Conjunct {
		private final Term mTerm;
		private final List<TermVariable> mVars;

		Conjunct(final Term term) {
			mTerm = term;
			final List<TermVariable> vars = new ArrayList<>(Arrays.asList(term.getFreeVars()));
			vars.sort(Comparator.comparing(TermVariable::getName).thenComparing(tv -> tv.getSort().toString()));
			mVars = List.copyOf(vars);
		}
	}

	/**
	 * {@code (select ... (select a i1) ... in) = value} for an array variable {@code a}.
	 */
	private static final class ArrayFact {
		private final List<Term> mIndices;
		private final Term mValue;

		ArrayFact(final List<Term> indices, final Term value) {
			mIndices = List.copyOf(indices);
			mValue = value;
		}
	}

	/**
	 * {@code lhs = rhs} where {@code target} occurs once in {@code lhs} and not in {@code rhs}, so that it defines
	 * {@code target} once all other variables have values; or {@code target = value} for a Boolean literal conjunct.
	 */
	private static final class Definition {
		private final TermVariable mTarget;
		private final Term mLhs;
		private final Term mRhs;
		// The variables other than the target that must have values first.
		private final Set<TermVariable> mRhsVars;
		private final IConcreteValue mValue;

		Definition(final TermVariable target, final Term lhs, final Term rhs) {
			mTarget = target;
			mLhs = lhs;
			mRhs = rhs;
			mRhsVars = new HashSet<>(Arrays.asList(rhs.getFreeVars()));
			mRhsVars.addAll(Arrays.asList(lhs.getFreeVars()));
			mRhsVars.remove(target);
			mValue = null;
		}

		Definition(final TermVariable target, final IConcreteValue value) {
			mTarget = target;
			mLhs = null;
			mRhs = null;
			mRhsVars = Set.of();
			mValue = value;
		}
	}
}
