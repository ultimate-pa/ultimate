/*
 * Copyright (C) 2015-2017 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator.EvalResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.OctagonRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.TVBool;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Octagon abstract state, based on A. Miné's "The octagon abstract domain"
 * (https://www-apr.lip6.fr/~mine/publi/article-mine-ast01.pdf). Octagons are a weakly relational abstract domain and
 * store constraints of the form "±x ± y ≤ c" for numerical (ints and reals) variables x, y and a constant c. Boolean
 * variables are stored separately, using the non-relation powerset domain. Other types (bit-vectors for instance) are
 * not supported.
 * <p>
 * {@linkplain OctDomainState}s appear to be immutable from the {@link FixpointEngine}'s point of view, but are mutable
 * for a better performance of the {@link OctPostOperator}. Do not modify any state that the {@linkplain FixpointEngine}
 * stores!
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public final class OctDomainState implements IAbstractState<OctDomainState> {

	private final static Comparator<IProgramVarOrConst> LEXICAL_VAR_COMPARATOR =
			(varA, varB) -> varA.getGloballyUniqueId().compareTo(varB.getGloballyUniqueId());

	/** Counter for created objects. Used to set {@link #mId}. */
	private static int sId;

	/** A human-readable hash code, unique for each object. */
	private final int mId;

	/** Function used to generate log strings. */
	private final Function<OctDomainState, String> mLogStringFunction;

	/**
	 * Indicates whether the state is bottom. This field is only used to determine whether a bottom state was created.
	 */
	private TVBool mIsBottom;

	/** Variables in this state {@link IProgramVarOrConst}. */
	private Set<IProgramVarOrConst> mVariables;

	/**
	 * Map of numerical variable (ints and reals) names to the index of the corresponding block row/column in the
	 * octagon matrix {@link #mNumericAbstraction}. Block row/column i contains the rows/columns 2i and 2i+1.
	 */
	private Map<IProgramVarOrConst, Integer> mMapNumericVarToIndex;

	/** Names of real-valued variables. */
	private Set<IProgramVarOrConst> mNumericNonIntVars;

	/** Abstract state for numeric variables (ints and reals). This is the actual octagon. */
	private OctMatrix mNumericAbstraction;

	/**
	 * Abstract state for boolean variables. This is a non-relational powerset domain and maps each boolean variable
	 * (name) to the set of values the variable can assume.
	 */
	private Map<IProgramVarOrConst, BoolValue> mBooleanAbstraction;

	private Map<Term, IProgramVarOrConst> mTerm2Vars;

	/**
	 * Creates a new, un-initialized abstract state. <b>Most attributes are not initialized and must be set by hand.</b>
	 *
	 * @param logStringFunction
	 *            Function to be used for creating log strings of this abstract state.
	 * @param isBottom
	 *            If <code>true</code>, the created state corresponds to &bot;, &top; otherwise.
	 */
	private OctDomainState(final Function<OctDomainState, String> logStringFunction, final TVBool isBottom) {
		mLogStringFunction = logStringFunction;
		mId = sId++;
		mIsBottom = isBottom;
	}

	/**
	 * Creates a new abstract state without any variables.
	 *
	 * @param logStringFunction
	 *            Function to be used for creating log strings of this abstract state.
	 * @return Empty octagon abstract state
	 */
	public static OctDomainState createFreshState(final Function<OctDomainState, String> logStringFunction) {
		return createFreshState(logStringFunction, false);
	}

	/**
	 * Creates a new abstract state without any variables.
	 *
	 * @param logStringFunction
	 *            Function to be used for creating log strings of this abstract state.
	 * @return Empty octagon abstract state
	 */
	public static OctDomainState createFreshState(final Function<OctDomainState, String> logStringFunction,
			final boolean isBottom) {
		final OctDomainState s = new OctDomainState(logStringFunction, isBottom ? TVBool.FIXED : TVBool.UNCHECKED);
		s.mVariables = new HashSet<>();
		s.mMapNumericVarToIndex = new HashMap<>();
		s.mNumericNonIntVars = new HashSet<>();
		s.mNumericAbstraction = OctMatrix.NEW;
		s.mBooleanAbstraction = new HashMap<>();
		return s;
	}

	/** @return Deep copy of this state */
	public OctDomainState deepCopy() {
		final OctDomainState s = new OctDomainState(mLogStringFunction, mIsBottom);
		s.mVariables = new HashSet<>(mVariables);
		s.mMapNumericVarToIndex = new HashMap<>(mMapNumericVarToIndex);
		s.mNumericNonIntVars = new HashSet<>(mNumericNonIntVars);
		s.mNumericAbstraction = mNumericAbstraction.copy();
		s.mBooleanAbstraction = new HashMap<>(mBooleanAbstraction);
		return s;
	}

	/**
	 * Creates a shallow copy of this OctagonDomainState. Use the {@code unref}... methods to deep-copy single fields
	 * before modifying them.
	 *
	 * @return shallow copy
	 *
	 * @see #unrefVariables(OctDomainState)
	 * @see #unrefOtherMapNumericVarToIndex(OctDomainState)
	 * @see #unrefOtherNumericNonIntVars(OctDomainState)
	 * @see #unrefOtherNumericAbstraction(OctDomainState)
	 * @see #unrefOtherBooleanAbstraction(OctDomainState)
	 */
	private OctDomainState shallowCopy() {
		final OctDomainState s = new OctDomainState(mLogStringFunction, mIsBottom);
		s.mVariables = mVariables;
		s.mMapNumericVarToIndex = mMapNumericVarToIndex;
		s.mNumericNonIntVars = mNumericNonIntVars;
		s.mNumericAbstraction = mNumericAbstraction;
		s.mBooleanAbstraction = mBooleanAbstraction;
		return s;
	}

	/**
	 * Deep-copy {@link #mVariables} to {@code other} state iff this and {@code other} share the same object. This state
	 * remains unchanged.
	 *
	 * @param other
	 *            State to be unreferenced from this state.
	 * @see shallowCopy()
	 */
	private void unrefVariables(final OctDomainState other) {
		if (other.mVariables == mVariables) {
			other.mVariables = new HashSet<>(mVariables);
		}
	}

	/**
	 * Deep-copy {@link #mMapNumericVarToIndex} to {@code other} state iff this and {@code other} share the same object.
	 * This state remains unchanged.
	 *
	 * @param other
	 *            State to be unreferenced from this state.
	 * @see shallowCopy()
	 */
	private void unrefOtherMapNumericVarToIndex(final OctDomainState other) {
		if (other.mMapNumericVarToIndex == mMapNumericVarToIndex) {
			other.mMapNumericVarToIndex = new HashMap<>(mMapNumericVarToIndex);
		}
	}

	/**
	 * Deep-copy {@link #mNumericNonIntVars} to {@code other} state iff this and {@code other} share the same object.
	 * This state remains unchanged.
	 *
	 * @param other
	 *            State to be unreferenced from this state.
	 * @see shallowCopy()
	 */
	private void unrefOtherNumericNonIntVars(final OctDomainState other) {
		if (other.mNumericNonIntVars == mNumericNonIntVars) {
			other.mNumericNonIntVars = new HashSet<>(mNumericNonIntVars);
		}
	}

	/**
	 * Deep-copy {@link #mBooleanAbstraction} to {@code other} state iff this and {@code other} share the same object.
	 * This state remains unchanged.
	 *
	 * @param other
	 *            State to be unreferenced from this state.
	 * @see shallowCopy()
	 */
	private void unrefOtherBooleanAbstraction(final OctDomainState other) {
		if (other.mBooleanAbstraction == mBooleanAbstraction) {
			other.mBooleanAbstraction = new HashMap<>(mBooleanAbstraction);
		}
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return Collections.unmodifiableSet(mVariables);
	}

	/**
	 * {@inheritDoc}
	 * <p>
	 * The returned state may contain shallow copies of this state's attributes. Do not modify!
	 */
	@Override
	public OctDomainState addVariable(final IProgramVarOrConst variable) {
		return addVariables(Collections.singleton(variable));
	}

	/**
	 * {@inheritDoc}
	 * <p>
	 * The returned state may contain shallow copies of this state's attributes. Do not modify!
	 */
	@Override
	public OctDomainState removeVariable(final IProgramVarOrConst variable) {
		return removeVariables(Collections.singleton(variable));
	}

	/**
	 * {@inheritDoc}
	 * <p>
	 * The returned state may contain shallow copies of this state's attributes. Do not modify!
	 */
	@Override
	public OctDomainState addVariables(final Collection<IProgramVarOrConst> variables) {
		final OctDomainState newState = shallowCopy();
		final Set<IProgramVarOrConst> addedNumVars = new HashSet<>();
		newState.mIsBottom = mIsBottom;
		if (variables.size() > 0) {
			unrefVariables(newState);
		}
		for (final IProgramVarOrConst newBoogieVar : variables) {
			if (!newState.mVariables.add(newBoogieVar)) {
				throw new IllegalArgumentException("Variable already present: " + newBoogieVar);
			}

			if (SmtSortUtils.isNumericSort(newBoogieVar.getSort())) {
				addedNumVars.add(newBoogieVar);
				if (SmtSortUtils.isRealSort(newBoogieVar.getSort())) {
					unrefOtherNumericNonIntVars(newState);
					newState.mNumericNonIntVars.add(newBoogieVar);
				}
			} else if (SmtSortUtils.isBoolSort(newBoogieVar.getSort())) {
				unrefOtherBooleanAbstraction(newState);
				newState.mBooleanAbstraction.put(newBoogieVar, BoolValue.TOP);
			}
			// else: variable has unsupported type and is assumed to be \top at all times
		}
		addNumericVariables(newState, addedNumVars);
		return newState;
	}

	private void addNumericVariables(final OctDomainState newState, final Set<IProgramVarOrConst> addedNumVars) {
		if (addedNumVars.isEmpty()) {
			return;
		}
		final SortedMap<IProgramVarOrConst, Integer> varsSortedByName = new TreeMap<>(LEXICAL_VAR_COMPARATOR);
		varsSortedByName.putAll(mMapNumericVarToIndex);
		addedNumVars.forEach(addedVar -> varsSortedByName.put(addedVar, -1));
		newState.mMapNumericVarToIndex = new HashMap<>();
		int index = 0;
		final int[] copyInstructions = new int[mMapNumericVarToIndex.size() + addedNumVars.size()];
		for (final Map.Entry<IProgramVarOrConst, Integer> varFromSourceIndex : varsSortedByName.entrySet()) {
			copyInstructions[index] = varFromSourceIndex.getValue();
			varFromSourceIndex.setValue(index);
			newState.mMapNumericVarToIndex.put(varFromSourceIndex.getKey(), index);
			++index;
		}
		newState.mNumericAbstraction = mNumericAbstraction.rearrange(copyInstructions);
	}

	/**
	 * {@inheritDoc}
	 * <p>
	 * The returned state may contain shallow copies of this state's attributes. Do not modify!
	 */
	@Override
	public OctDomainState removeVariables(final Collection<IProgramVarOrConst> variables) {

		final OctDomainState newState = shallowCopy();
		final Set<Integer> indexRemovedNumericVars = new HashSet<>();
		for (final IProgramVarOrConst name : variables) {
			unrefVariables(newState);
			newState.mVariables.remove(name);
			if (newState.mMapNumericVarToIndex.containsKey(name)) {
				unrefOtherMapNumericVarToIndex(newState);
				final int i = newState.mMapNumericVarToIndex.remove(name);
				indexRemovedNumericVars.add(i);
				if (mNumericNonIntVars.contains(name)) {
					unrefOtherNumericNonIntVars(newState);
					newState.mNumericNonIntVars.remove(name);
				}
			} else if (mBooleanAbstraction.containsKey(name)) {
				unrefOtherBooleanAbstraction(newState);
				newState.mBooleanAbstraction.remove(name);
			}
			// else: variable had an unsupported type => its abstract value (\top) wasn't stored explicitly
			// or variable was not stored at all => already removed
		}
		if (!indexRemovedNumericVars.isEmpty()) {
			newState.mNumericAbstraction = cachedSelectiveClosure().removeVariables(indexRemovedNumericVars);
			// already unref'd
			defragmentMap(newState.mMapNumericVarToIndex);
		}
		return newState;
	}

	@Override
	public OctDomainState renameVariables(final Map<IProgramVarOrConst, IProgramVarOrConst> old2NewVars) {
		if (old2NewVars == null || old2NewVars.isEmpty()) {
			return this;
		}

		// sanitize input
		final Map<IProgramVarOrConst, IProgramVarOrConst> sanitizedOld2NewVars = new HashMap<>(old2NewVars);
		for (final Entry<IProgramVarOrConst, IProgramVarOrConst> entry : old2NewVars.entrySet()) {
			final IProgramVarOrConst oldVar = entry.getKey();
			final IProgramVarOrConst newVar = entry.getValue();

			if (newVar == null) {
				throw new IllegalArgumentException("Cannot rename " + oldVar + " to null");
			}

			if (oldVar == newVar) {
				// we do not need to rename to itself
				sanitizedOld2NewVars.remove(oldVar);
			}

			if (!mVariables.contains(oldVar)) {
				// we do not need to rename if variable is not present
				sanitizedOld2NewVars.remove(oldVar);
			}
		}

		if (sanitizedOld2NewVars.isEmpty()) {
			return this;
		}

		// create new state with independent mVariables and update mVariables
		final OctDomainState newState = shallowCopy();
		unrefVariables(newState);
		sanitizedOld2NewVars.entrySet().stream().forEach(a -> {
			newState.mVariables.remove(a.getKey());
			newState.mVariables.add(a.getValue());
		});

		// partition in boolean and non-boolean variables
		final List<Entry<IProgramVarOrConst, IProgramVarOrConst>> booleanOld2NewVars = sanitizedOld2NewVars.entrySet()
				.stream().filter(a -> mBooleanAbstraction.containsKey(a.getKey())).collect(Collectors.toList());
		final List<Entry<IProgramVarOrConst, IProgramVarOrConst>> numericOld2NewVars = sanitizedOld2NewVars.entrySet()
				.stream().filter(a -> mMapNumericVarToIndex.containsKey(a.getKey())).collect(Collectors.toList());
		// note: variables that are neither boolean nor numeric are of unsupported type and treated as always top

		// rename boolean abstraction
		if (!booleanOld2NewVars.isEmpty()) {
			unrefOtherBooleanAbstraction(newState);
			booleanOld2NewVars.stream().forEach(a -> {
				final BoolValue value = newState.mBooleanAbstraction.remove(a.getKey());
				newState.mBooleanAbstraction.put(a.getValue(), value);
			});
		}

		// if we only needed to rename bools, we are finished
		if (numericOld2NewVars.isEmpty()) {
			return newState;
		}

		// get nonint-variables in numeric variables and update mNumericNonIntVars if necessary
		final List<Entry<IProgramVarOrConst, IProgramVarOrConst>> numericNonIntOld2NewVars = numericOld2NewVars.stream()
				.filter(a -> mNumericNonIntVars.contains(a.getKey())).collect(Collectors.toList());
		if (!numericNonIntOld2NewVars.isEmpty()) {
			unrefOtherNumericNonIntVars(newState);
			numericNonIntOld2NewVars.stream().forEach(a -> {
				newState.mNumericNonIntVars.remove(a.getKey());
				newState.mNumericNonIntVars.add(a.getValue());
			});
		}

		// update mMapNumericVarToIndex
		unrefOtherMapNumericVarToIndex(newState);
		numericOld2NewVars.stream().forEach(a -> {
			final Integer idx = newState.mMapNumericVarToIndex.remove(a.getKey());
			newState.mMapNumericVarToIndex.put(a.getValue(), idx);

		});

		// create new sorting for matrix
		final SortedMap<IProgramVarOrConst, Integer> varsSortedByName = new TreeMap<>(LEXICAL_VAR_COMPARATOR);
		varsSortedByName.putAll(newState.mMapNumericVarToIndex);
		final int[] copyInstructions = new int[newState.mMapNumericVarToIndex.size()];
		newState.mMapNumericVarToIndex = new HashMap<>();
		int index = 0;
		for (final Entry<IProgramVarOrConst, Integer> varFromSourceIndex : varsSortedByName.entrySet()) {
			copyInstructions[index] = varFromSourceIndex.getValue();
			varFromSourceIndex.setValue(index);
			newState.mMapNumericVarToIndex.put(varFromSourceIndex.getKey(), index);
			++index;
		}

		// determine if we need to rearrange the matrix
		for (int i = 0; i < copyInstructions.length; ++i) {
			if (copyInstructions[i] != i) {
				// note: rearrange creates a fresh matrix
				newState.mNumericAbstraction = mNumericAbstraction.rearrange(copyInstructions);
				break;
			}
		}

		return newState;
	}

	/**
	 * Defragments a map with {@code n} entries so that the resulting map's domain are the {@code n} first natural
	 * numbers <code>{0, 1, 2, ..., n-1}</code>. The order of the old map remains the same, meaning that the map key
	 * with the smallest value will have the defragmented value {@code 0}.
	 *
	 * @param map
	 *            Arbitrary map with integer values
	 */
	private static <T> void defragmentMap(final Map<T, Integer> map) {
		final TreeMap<Integer, T> reversedMapSortedAscending = new TreeMap<>();
		for (final Map.Entry<T, Integer> entry : map.entrySet()) {
			reversedMapSortedAscending.put(entry.getValue(), entry.getKey());
		}
		map.clear();
		int newIndex = 0;
		for (final Map.Entry<Integer, T> entry : reversedMapSortedAscending.entrySet()) {
			map.put(entry.getValue(), newIndex);
			++newIndex;
		}
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		return mVariables.contains(var);
	}

	@Override
	public boolean isEmpty() {
		return mVariables.isEmpty();
	}

	@Override
	public boolean isBottom() {
		switch (mIsBottom) {
		case FALSE:
			return false;
		case TRUE:
		case FIXED:
			return true;
		case UNCHECKED:
			final boolean isBottom = isBooleanAbstractionBottom() || isNumericAbstractionBottom();
			mIsBottom = isBottom ? TVBool.TRUE : TVBool.FALSE;
			return isBottom;
		default:
			throw new UnsupportedOperationException("Unknown LBool " + mIsBottom);
		}
	}

	/** @return The numeric abstraction represents no concrete states */
	private boolean isNumericAbstractionBottom() {
		return cachedSelectiveClosure().hasNegativeSelfLoop();
	}

	/** @return The boolean abstraction represents no concrete states */
	private boolean isBooleanAbstractionBottom() {
		return mBooleanAbstraction.containsValue(BoolValue.BOT);
	}

	/**
	 * Returns the strong closure of the octagon (numerical abstraction) or the tight closure, if all numerical
	 * variables are integers.
	 * <p>
	 * The closure is cached after the first computation. The original cache is returned. Modifications of returned
	 * octagon may also effect other {@linkplain OctDomainState}!
	 *
	 * @return Strong or tight closure of the octagon, depending on the types of numerical variables in this state
	 */
	private OctMatrix cachedSelectiveClosure() {
		if (isNumericAbstractionIntegral()) {
			return mNumericAbstraction.cachedTightClosure();
		}
		return mNumericAbstraction.cachedStrongClosure();
	}

	/**
	 * Returns the best available/cached closure of the octagon (numerical abstraction).
	 * <p>
	 * If all numerical variables in this state are integers and the tight closure is cached, then the tight closure is
	 * returned. Otherwise, the strong closure is returned if it is cached. If no closure is cached, then the original
	 * octagon is returned.
	 * <p>
	 * The original cache is returned. Modifications of returned octagon may also effect other
	 * {@linkplain OctDomainState}!
	 *
	 * @return Best available/cached closure
	 */
	private OctMatrix bestAvailableClosure() {
		if (isNumericAbstractionIntegral() && mNumericAbstraction.hasCachedTightClosure()) {
			return mNumericAbstraction.cachedTightClosure();
		} else if (mNumericAbstraction.hasCachedStrongClosure()) {
			return mNumericAbstraction.cachedStrongClosure();
		}
		return mNumericAbstraction;
	}

	/** @return All numerical variables in this state are integers */
	private boolean isNumericAbstractionIntegral() {
		return mNumericNonIntVars.isEmpty();
	}

	@Override
	public boolean isEqualTo(final OctDomainState other) {
		if (other == null) {
			return false;
		} else if (other == this) {
			return true;
		} else {
			final boolean isEqual = mVariables.equals(other.mVariables)
					&& mBooleanAbstraction.equals(other.mBooleanAbstraction) && numericAbstractionIsEqualTo(other);
			return isEqual;
		}
	}

	@Override
	public SubsetResult isSubsetOf(final OctDomainState other) {
		if (isBottom() && other.isBottom()) {
			return SubsetResult.EQUAL;
		}
		if (isBottom()) {
			return SubsetResult.STRICT;
		}
		if (other.isBottom()) {
			return SubsetResult.NONE;
		}

		for (final Entry<IProgramVarOrConst, BoolValue> thisEntry : mBooleanAbstraction.entrySet()) {
			final BoolValue thisVal = thisEntry.getValue();
			final BoolValue otherVal = other.mBooleanAbstraction.get(thisEntry.getKey());
			if (otherVal == null) {
				// if the other state has no value for this value, it means top for the other state
				continue;
			}
			if (!thisVal.isSubsetEqual(otherVal)) {
				return SubsetResult.NONE;
			}
		}

		if (!cachedSelectiveClosure().elementwiseRelation(other.mNumericAbstraction,
				OctMatrix.sRelationLessThanOrEqual)) {
			// no need to use other.closure
			return SubsetResult.NONE;
		}
		return SubsetResult.NON_STRICT;
	}

	@Override
	public int hashCode() {
		return mId;
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
		final OctDomainState other = (OctDomainState) obj;
		return mId == other.mId;
	}

	/** For internal use in {@link #isEqualTo(OctDomainState)}. */
	private boolean numericAbstractionIsEqualTo(final OctDomainState other) {
		assert mMapNumericVarToIndex.keySet().equals(other.mMapNumericVarToIndex.keySet());
		final OctMatrix thisClosure = cachedSelectiveClosure();
		final OctMatrix otherClosure = other.cachedSelectiveClosure();
		final boolean thisIsBottom = thisClosure.hasNegativeSelfLoop();
		final boolean otherIsBottom = otherClosure.hasNegativeSelfLoop();
		if (thisIsBottom != otherIsBottom) {
			return false;
		} else if (thisIsBottom) {
			return true;
		}
		return thisClosure.isEqualTo(otherClosure);
	}

	/**
	 * Creates an over-approximation of the intersection of this and another abstract state.
	 * <p>
	 * The returned state may contain shallow copies of this state's attributes. Do not modify!
	 *
	 * @param other
	 *            Abstract state with same variables as this one
	 * @return Over-approximated intersection
	 */
	@Override
	public OctDomainState intersect(final OctDomainState other) {
		final OctMatrix numResult = OctMatrix.min(bestAvailableClosure(), other.bestAvailableClosure());
		return operation(other, BoolValue::intersect, numResult);
	}

	/**
	 * Creates an over-approximation of the union of this and another abstract state.
	 * <p>
	 * The returned state may contain shallow copies of this state's attributes. Do not modify!
	 *
	 * @param other
	 *            Abstract state with same variables as this one
	 * @return Over-approximated union
	 */
	@Override
	public OctDomainState union(final OctDomainState other) {
		if (isBottom()) {
			return other;
		}
		if (other.isBottom()) {
			return this;
		}
		final OctMatrix numResult = OctMatrix.max(bestAvailableClosure(), other.bestAvailableClosure());
		return operation(other, BoolValue::union, numResult);
	}

	/**
	 * Creates an over-approximation of the union of this and another abstract state using a given widening operator for
	 * octagons.
	 * <p>
	 * The returned state may contain shallow copies of this state's attributes. Do not modify!
	 *
	 * @param other
	 *            Abstract state with same variables as this one
	 * @param widenOp
	 *            Widening operator, used to combine this octagon with the other octagon. Should not modify existing
	 *            abstractions. {@code this}, {@code other} --> {@code result}
	 * @return Over-approximated union
	 */
	public OctDomainState widen(final OctDomainState other, final BiFunction<OctMatrix, OctMatrix, OctMatrix> widenOp) {
		// left argument of widening operation must not be closed (or widening may not stabilize)!
		final OctMatrix numResult = widenOp.apply(mNumericAbstraction, other.bestAvailableClosure());
		return operation(other, BoolValue::union, numResult);
	}

	/**
	 * Performs an operation (for instance join, meet, or widen) on the boolean abstraction of this and another abstract
	 * state. The octagon (numerical abstraction) of the resulting abstract state is given as an argument.
	 * <p>
	 * The returned state may contain shallow copies of this state's attributes. Do not modify!
	 *
	 * @param other
	 *            Abstract state with same variables as this one
	 * @param booleanOperation
	 *            Operation on the boolean abstractions. Should not modify existing abstractions. {@code this},
	 *            {@code other} --> {@code result}
	 * @param numericAbstractionResult
	 * @return Result of the operation
	 */
	private OctDomainState operation(final OctDomainState other,
			final BiFunction<BoolValue, BoolValue, BoolValue> booleanOperation,
			final OctMatrix numericAbstractionResult) {
		assert assertNotBottomBeforeAssign();
		assert other.assertNotBottomBeforeAssign();
		final OctDomainState result = shallowCopy();
		for (final Entry<IProgramVarOrConst, BoolValue> entry : mBooleanAbstraction.entrySet()) {
			final IProgramVarOrConst name = entry.getKey();
			final BoolValue oldValue = entry.getValue();
			final BoolValue newValue = booleanOperation.apply(oldValue, other.mBooleanAbstraction.get(name));
			if (!oldValue.equals(newValue)) {
				unrefOtherBooleanAbstraction(result);
				result.mBooleanAbstraction.put(name, newValue);
			}
		}
		result.mNumericAbstraction = numericAbstractionResult;
		result.mIsBottom = TVBool.UNCHECKED;
		return result;
	}

	@Override
	public Term getTerm(final Script script) {
		if (isBottom()) {
			return script.term("false");
		}

		final List<Term> terms = new ArrayList<>();
		terms.addAll(getTermNumericAbstraction(script));
		terms.addAll(getTermBooleanAbstraction(script));
		return SmtUtils.and(script, terms);
	}

	/** For internal use in {@link #getTerm(Script))}. */
	private List<Term> getTermNumericAbstraction(final Script script) {
		final Term[] mapIndexToTerm = new Term[mMapNumericVarToIndex.size()];
		for (final Entry<IProgramVarOrConst, Integer> entry : mMapNumericVarToIndex.entrySet()) {
			final Term termVar = getTermVar(entry.getKey());
			mapIndexToTerm[entry.getValue()] = termVar;
		}
		return cachedSelectiveClosure().getTerm(script, mapIndexToTerm);
	}

	/** For internal use in {@link #getTerm(Script))}. */
	private List<Term> getTermBooleanAbstraction(final Script script) {
		final List<Term> resultTerm = new ArrayList<>(mBooleanAbstraction.size());
		for (final Entry<IProgramVarOrConst, BoolValue> entry : mBooleanAbstraction.entrySet()) {
			final Term termVar = getTermVar(entry.getKey());
			final Sort sort = termVar.getSort().getRealSort();
			final Term newTerm = entry.getValue().getTerm(script, sort, termVar);
			resultTerm.add(newTerm);
		}
		return resultTerm;
	}

	/**
	 * Finds the SMT term variable for a given variable name.
	 *
	 * @param varName
	 *            Name of a variable from this abstract state
	 * @return SMT term variable corresponding to the given variable name
	 */
	private static Term getTermVar(final IProgramVarOrConst var) {
		if (var instanceof IProgramVar) {
			return ((IProgramVar) var).getTermVariable();
		} else if (var instanceof BoogieConst) {
			return ((BoogieConst) var).getDefaultConstant();
		}
		return null;
	}

	/**
	 * {@inheritDoc}.
	 * <p>
	 * The returned state is a shallow copy of this state. Do not modify!
	 */
	@Override
	public OctDomainState patch(final OctDomainState dominator) {
		assert assertNotBottomBeforeAssign();
		final OctDomainState patchedState = shallowCopy();
		patchedState.mIsBottom = TVBool.UNCHECKED;
		final SortedMap<IProgramVarOrConst, Integer> mapNumVarsToDominatorIndices =
				new TreeMap<>(LEXICAL_VAR_COMPARATOR);
		mMapNumericVarToIndex.entrySet()
				.forEach(varToOldIndex -> mapNumVarsToDominatorIndices.put(varToOldIndex.getKey(), null)); // patched
																											// variables
																											// will be
																											// overwritten
																											// later

		for (final IProgramVarOrConst newBoogieVar : dominator.mVariables) {
			unrefVariables(patchedState);
			final boolean varIsNew = patchedState.mVariables.add(newBoogieVar);
			assert varIsNew || mVariables.contains(newBoogieVar);
			if (SmtSortUtils.isNumericSort(newBoogieVar.getSort())) {
				final int sourceVar = dominator.mMapNumericVarToIndex.get(newBoogieVar);
				mapNumVarsToDominatorIndices.put(newBoogieVar, sourceVar);
				if (varIsNew) {
					if (SmtSortUtils.isRealSort(newBoogieVar.getSort())) {
						unrefOtherNumericNonIntVars(patchedState);
						patchedState.mNumericNonIntVars.add(newBoogieVar);
					}
				}
			} else if (SmtSortUtils.isBoolSort(newBoogieVar.getSort())) {
				unrefOtherBooleanAbstraction(patchedState);
				patchedState.mBooleanAbstraction.put(newBoogieVar, dominator.mBooleanAbstraction.get(newBoogieVar));
			}
			// else: variable has unsupported type and is assumed to be \top
		}
		final int[] mapNumVarsToOldIndices = new int[mapNumVarsToDominatorIndices.size()];
		final Map<Integer, Integer> mapNumVarIndicesToDominatorIndices = new HashMap<>();
		final Iterator<Map.Entry<IProgramVarOrConst, Integer>> iter =
				mapNumVarsToDominatorIndices.entrySet().iterator();
		patchedState.mMapNumericVarToIndex = new HashMap<>();
		int index = 0;
		while (iter.hasNext()) {
			final Map.Entry<IProgramVarOrConst, Integer> entry = iter.next();
			final IProgramVarOrConst var = entry.getKey();
			final Integer indexInDominator = entry.getValue();
			if (indexInDominator == null) {
				// variable is old (from this octagon only)
				mapNumVarsToOldIndices[index] = mMapNumericVarToIndex.get(var);
			} else {
				// variable is fresh or will be patched (from the dominator)
				mapNumVarsToOldIndices[index] = -1;
				mapNumVarIndicesToDominatorIndices.put(index, indexInDominator);
			}
			patchedState.mMapNumericVarToIndex.put(var, index);
			++index;
		}
		// TODO rearrange() writes INF values which get overwritten by copy selection() --> optimize
		patchedState.mNumericAbstraction = cachedSelectiveClosure().rearrange(mapNumVarsToOldIndices);
		patchedState.mNumericAbstraction.copySelection(dominator.bestAvailableClosure(),
				mapNumVarIndicesToDominatorIndices);
		return patchedState;
	}

	/**
	 * Copies values from a set of variables in a source abstract state to set of variables in this abstract state. The
	 * result is a new abstract state. This abstract state remains unchanged. Global variables and constants that are
	 * shared between the {@code source} abstract state and this abstract state are always copied. This models the
	 * effect of calling procedures or returning from them.
	 * <p>
	 * The returned state may contain shallow copies of this state's attributes. Do not modify!
	 *
	 * @param source
	 *            State to copies values from.
	 * @param mapTargetToSource
	 *            Map of variables to be copied. The keys are the names of variables in the source state. The values are
	 *            the names of variables in this state.
	 * @return (Shallow) copy of this state, where the specified variables and global variables are overwritten with the
	 *         values from {@code source} abstract state.
	 */
	public OctDomainState copyValuesOnScopeChange(final OctDomainState source,
			final List<Pair<IProgramVarOrConst, IProgramVarOrConst>> mapTargetToSource, final boolean alsoCopyOldVars) {

		assert assertNotBottomBeforeAssign();
		// TODO closure in advance to reduce information loss

		final Map<Integer, Integer> mapNumericTargetToSource = new HashMap<>();
		final List<Pair<IProgramVarOrConst, IProgramVarOrConst>> mapBooleanTargetToSource =
				new ArrayList<>(mapTargetToSource.size());

		// shared (=global) numeric variables (copy to keep relations between globals and in/out-parameters)
		Set<IProgramVarOrConst> sharedVars;
		if (alsoCopyOldVars) {
			sharedVars = sharedGlobalVars(source);
		} else {
			sharedVars =
					sharedGlobalVars(source).stream().filter(a -> !AbsIntUtil.isOldVar(a)).collect(Collectors.toSet());
		}

		for (final IProgramVarOrConst var : sharedVars) {
			final Integer targetIndex = mMapNumericVarToIndex.get(var);
			if (targetIndex != null) {
				final Integer sourceIndex = source.mMapNumericVarToIndex.get(var);
				assert sourceIndex != null : "shared variables are not really shared";
				mapNumericTargetToSource.put(targetIndex, sourceIndex);
			}
			// do not copy shared (=global) booleans (again). Already done by patch(...).
		}

		// in/out-parameters (from one scope) to locals (from another scope)
		for (final Pair<IProgramVarOrConst, IProgramVarOrConst> assignmentPair : mapTargetToSource) {
			final IProgramVarOrConst targetVar = assignmentPair.getFirst();
			final IProgramVarOrConst sourceVar = assignmentPair.getSecond();
			final Integer targetIndex = mMapNumericVarToIndex.get(targetVar);
			if (targetIndex != null) {
				final Integer sourceIndex = source.mMapNumericVarToIndex.get(sourceVar);
				assert sourceIndex != null : "assigned non-numeric var to numeric var";
				mapNumericTargetToSource.put(targetIndex, sourceIndex);
			} else if (mBooleanAbstraction.containsKey(targetVar)) {
				assert source.mBooleanAbstraction.containsKey(sourceVar) : "assigned non-boolean var to boolean var";
				mapBooleanTargetToSource.add(new Pair<>(targetVar, sourceVar));
			}
		}

		// create new state
		final OctDomainState newState = shallowCopy();
		newState.mIsBottom = TVBool.UNCHECKED;
		if (!mapNumericTargetToSource.isEmpty()) {
			newState.mNumericAbstraction = cachedSelectiveClosure().copy();
			newState.mNumericAbstraction.copySelection(source.bestAvailableClosure(), mapNumericTargetToSource);
		}
		if (!mapBooleanTargetToSource.isEmpty()) {
			unrefOtherBooleanAbstraction(newState);
			for (final Pair<IProgramVarOrConst, IProgramVarOrConst> entry : mapBooleanTargetToSource) {
				final IProgramVarOrConst targetVar = entry.getFirst();
				final IProgramVarOrConst sourceVar = entry.getSecond();
				final BoolValue sourceValue = source.mBooleanAbstraction.get(sourceVar);
				newState.mBooleanAbstraction.put(targetVar, sourceValue);
			}
		}
		return newState;
	}

	/**
	 * Finds global variables and constants that are both present in this and another abstract state.
	 *
	 * @param other
	 *            Other abstract state.
	 * @return Names of global variables and constants, shared by both states
	 */
	public Set<IProgramVarOrConst> sharedGlobalVars(final OctDomainState other) {
		final Set<IProgramVarOrConst> sharedVars = new HashSet<>();
		final Set<IProgramVarOrConst> otherEntrySet = other.mVariables;
		for (final IProgramVarOrConst entry : mVariables) {
			if (AbsIntUtil.isGlobal(entry) && otherEntrySet.contains(entry)) {
				sharedVars.add(entry);
			}
		}
		return sharedVars;
	}

	/**
	 * Removes all constraints for a variable.
	 * <p>
	 * Modifies this state in-place.
	 *
	 * @param var
	 *            Name of a variable.
	 */
	protected void havocVar(final IProgramVarOrConst var) {
		havocVars(Collections.singleton(var));
	}

	/**
	 * Removes all constrains for a set of variables.
	 * <p>
	 * Modifies this state in-place.
	 *
	 * @param vars
	 *            Names of variables.
	 */
	protected void havocVars(final Collection<IProgramVarOrConst> vars) {
		// TODO Only calculate closure if necessary. Some vars may have no constraints to other vars => no closure
		assert assertNotBottomBeforeAssign();
		mIsBottom = TVBool.UNCHECKED;
		final Set<Integer> numVarIndices = new HashSet<>();
		for (final IProgramVarOrConst var : vars) {
			final Integer numVarIndex = mMapNumericVarToIndex.get(var);
			if (numVarIndex != null) {
				numVarIndices.add(numVarIndex);
			} else if (mBooleanAbstraction.containsKey(var)) {
				mBooleanAbstraction.put(var, BoolValue.TOP);
			}
			// else: variables of unsupported types are assumed to be \top all the time
			assert mVariables.contains(var) : "unknown variable in havoc: " + var;
		}
		if (!numVarIndices.isEmpty()) {
			mNumericAbstraction = cachedSelectiveClosure().copy();
			numVarIndices.forEach(v -> mNumericAbstraction.havocVar(v));
		}
	}

	/**
	 * Updates this abstract state according to the assignment {@code v := v + c} for a variable {@code v} and a
	 * constant {@code c}.
	 * <p>
	 * Modifies this state in-place.
	 *
	 * @param targetVar
	 *            Variable to be incremented
	 * @param addConstant
	 *            Constant to be added (must not be infinity)
	 */
	protected void incrementNumericVar(final IProgramVarOrConst targetVar, final OctValue addConstant) {
		assert assertNotBottomBeforeAssign();
		mIsBottom = TVBool.UNCHECKED;
		mNumericAbstraction.incrementVar(numVarIndex(targetVar), addConstant);
	}

	/**
	 * Updates this abstract state according to the assignment {@code v := -v}.
	 * <p>
	 * Modifies this state in-place.
	 *
	 * @param targetVar
	 *            Variable to be negated
	 */
	protected void negateNumericVar(final IProgramVarOrConst targetVar) {
		assert assertNotBottomBeforeAssign();
		mIsBottom = TVBool.UNCHECKED;
		mNumericAbstraction.negateVar(numVarIndex(targetVar));
	}

	/**
	 * Updates this abstract state according to the assignment {@code v := c} for a variable {@code v} and a constant
	 * {@code c}.
	 * <p>
	 * Modifies this state in-place.
	 *
	 * @param targetVar
	 *            Variable to be assigned
	 * @param constant
	 *            Assigned constant
	 */
	protected void assignNumericVarConstant(final IProgramVarOrConst targetVar, final OctValue constant) {
		assert assertNotBottomBeforeAssign();
		mIsBottom = TVBool.UNCHECKED;
		mNumericAbstraction = cachedSelectiveClosure().copy();
		mNumericAbstraction.assignVarConstant(numVarIndex(targetVar), constant);
	}

	/**
	 * Updates this abstract state according to {@code havoc v; assume min <= v && v <= max;} for a variable {@code v}
	 * and an interval {@code [min, max]}.
	 * <p>
	 * Modifies this state in-place.
	 *
	 * @param targetVar
	 *            Variable to be assigned
	 * @param interval
	 *            Assigned interval
	 */
	protected void assignNumericVarInterval(final IProgramVarOrConst targetVar, final OctInterval interval) {
		assert assertNotBottomBeforeAssign();
		mIsBottom = TVBool.UNCHECKED;
		mNumericAbstraction = cachedSelectiveClosure().copy();
		mNumericAbstraction.assignVarInterval(numVarIndex(targetVar), interval.getMin(), interval.getMax());
	}

	/**
	 * Updates this abstract state according to {@code assume v == c;} for a variable {@code v} and a constant {@code c}
	 * .
	 * <p>
	 * Modifies this state in-place.
	 *
	 * @param targetVar
	 *            Variable to be assumed
	 * @param constant
	 *            Assumed constant
	 */
	protected void assumeNumericVarConstant(final IProgramVarOrConst targetVar, final OctValue constant) {
		assert assertNotBottomBeforeAssign();
		mIsBottom = TVBool.UNCHECKED;
		mNumericAbstraction.assumeVarConstant(numVarIndex(targetVar), constant);
	}

	/**
	 * Updates this abstract state according to {@code assume min <= v && v <= max;} for a variable {@code v} and an
	 * interval {@code [min, max]}.
	 * <p>
	 * Modifies this state in-place.
	 *
	 * @param targetVar
	 *            Variable to be assumed
	 * @param constant
	 *            Assumed interval
	 */
	protected void assumeNumericVarInterval(final IProgramVarOrConst targetVar, final OctValue min,
			final OctValue max) {
		assert assertNotBottomBeforeAssign();
		mIsBottom = TVBool.UNCHECKED;
		mNumericAbstraction.assumeVarInterval(numVarIndex(targetVar), min, max);
	}

	/**
	 * Updates this abstract state according to {@code assume ± var1 ± var2 <= c;} for variables {@code var1} and
	 * {@code var2} and a constant {@code c}.
	 * <p>
	 * Modifies this state in-place.
	 *
	 * @param var1
	 *            First variable
	 * @param var1Negate
	 *            The sign of {@code var1} is negative
	 * @param var2
	 *            Second variable
	 * @param var2Negate
	 *            The sign of {@code var2} is negative
	 * @param constant
	 *            Constant upper bound
	 */
	protected void assumeNumericVarRelationLeConstant(final IProgramVarOrConst var1, final boolean var1Negate,
			final IProgramVarOrConst var2, final boolean var2Negate, final OctValue constant) {
		assert assertNotBottomBeforeAssign();
		mIsBottom = TVBool.UNCHECKED;
		mNumericAbstraction.assumeVarRelationLeConstant(numVarIndex(var1), var1Negate, numVarIndex(var2), var2Negate,
				constant);
	}

	/**
	 * Projects a variable of this abstract state to an interval.
	 *
	 * @param numericVar
	 *            Variable to be projected
	 * @return Valid values the variable as an interval
	 */
	public OctInterval projectToInterval(final IProgramVarOrConst numericVar) {
		return OctInterval.fromMatrix(cachedSelectiveClosure(), numVarIndex(numericVar));
	}

	/**
	 * Projects an expression of the form {@code assume ± var1 ± var2} (for variables {@code var1} and {@code var2} and
	 * a constant {@code c}) to an interval.
	 *
	 * @param tvf
	 *            Affine expression in "two variable form"
	 * @return Valid values of the expression as an interval
	 */
	public OctInterval projectToInterval(final AffineExpression.TwoVarForm tvf) {
		int iVar1 = mMapNumericVarToIndex.get(tvf.var1) * 2;
		// inverted form, because x-(-y) = x+y
		int iVar2Inv = mMapNumericVarToIndex.get(tvf.var2) * 2 + 1;
		if (tvf.negVar1) {
			iVar1 = iVar1 + 1;
		}
		if (tvf.negVar2) {
			iVar2Inv = iVar2Inv - 1;
		}
		final OctMatrix m = cachedSelectiveClosure();
		// var1 - (-var2) ≤ c equivalent var1 + var2 ≤ c
		OctValue max = m.get(iVar2Inv, iVar1);
		// (-var1) - var2 ≤ c equivalent -c ≤ var1 + var2
		OctValue min = m.get(iVar2Inv ^ 1, iVar1 ^ 1).negateIfNotInfinity();
		if (tvf.constant.signum() != 0) {
			max = max.add(tvf.constant);
			min = min.add(tvf.constant);
		}
		return new OctInterval(min, max);
	}

	public EvalResult evaluate(final Script script, final Term term) {
		if (isBottom() || SmtUtils.isTrueLiteral(term)) {
			return EvalResult.TRUE;
		}
		if (SmtUtils.isFalseLiteral(term)) {
			return EvalResult.FALSE;
		}
		final OctagonRelation octRel;
		final PolynomialRelation polyRel = PolynomialRelation.convert(script, term);
		if (polyRel == null || !polyRel.isAffine()) {
			//term is not an affine relation
			return EvalResult.UNKNOWN; // alternatively apply SMT solver
			// TODO (optional) special treatment for boolean variables
		}
		octRel = OctagonRelation.from(polyRel);
		if (octRel == null) {
			return EvalResult.UNKNOWN; // alternatively apply SMT solver
		}
		mNumericAbstraction = cachedSelectiveClosure();

		final int var1Idx =
				2 * mMapNumericVarToIndex.get(getVariable(octRel.getVar1())) + (octRel.isNegateVar1() ? 1 : 0);
		final int var2Idx =
				2 * mMapNumericVarToIndex.get(getVariable(octRel.getVar2())) + (octRel.isNegateVar2() ? 1 : 0);

		return OctInterval.fromMatrix(mNumericAbstraction, var1Idx, var2Idx).evaluate(octRel.getRelationSymbol(),
				octRel.getConstant());
	}

	private IProgramVarOrConst getVariable(final Term term) {
		if (mTerm2Vars == null) {
			mTerm2Vars = new HashMap<>();
			for (final IProgramVarOrConst key : mMapNumericVarToIndex.keySet()) {
				mTerm2Vars.put(key.getTerm(), key);
			}
			for (final IProgramVarOrConst key : mBooleanAbstraction.keySet()) {
				mTerm2Vars.put(key.getTerm(), key);
			}
		}
		final IProgramVarOrConst result = mTerm2Vars.get(term);
		if (result == null) {
			throw new AssertionError("Unknown variable for the term " + term);
		}
		return result;
	}

	/**
	 * Returns the index of an numerical variable of this abstract state for the octagon. A variable with index i
	 * corresponds to the octagon columns/rows 2i and 2i+1.
	 *
	 * @param var
	 *            Variable
	 * @return Index of the variable for the octagon
	 */
	private int numVarIndex(final IProgramVarOrConst var) {
		final Integer index = mMapNumericVarToIndex.get(var);
		assert index != null : "Not a numeric variable: " + var;
		return index;
	}

	/**
	 * Updates this abstract state according to {@code a := x;  b := y;  ...}. for variables {@code a}, {@code b},
	 * {@code x}, {@code y}. The assignments are sequential in the iteration order of the given map.
	 * <p>
	 * Modifies this state in-place.
	 *
	 * @param mapTargetVarToSourceVar
	 */
	protected void copyVars(final List<Pair<IProgramVarOrConst, IProgramVarOrConst>> mapTargetVarToSourceVar) {
		assert assertNotBottomBeforeAssign();
		mIsBottom = TVBool.UNCHECKED;
		boolean usedClosure = false;

		for (final Pair<IProgramVarOrConst, IProgramVarOrConst> entry : mapTargetVarToSourceVar) {
			final IProgramVarOrConst targetVar = entry.getFirst();
			final IProgramVarOrConst sourceVar = entry.getSecond();

			final Integer targetIndex = mMapNumericVarToIndex.get(targetVar);
			if (targetIndex != null) {
				if (!usedClosure) {
					mNumericAbstraction = cachedSelectiveClosure().copy();
					usedClosure = true;
				}
				final Integer sourceIndex = mMapNumericVarToIndex.get(sourceVar);
				assert sourceIndex != null : "Incompatible types: " + sourceVar + " (" + sourceVar.getSort()
						+ ") has no matching target";
				mNumericAbstraction.assignVarCopy(targetIndex, sourceIndex);

			} else if (mBooleanAbstraction.containsKey(targetVar)) {
				final BoolValue value = mBooleanAbstraction.get(sourceVar);
				assert value != null : "Incompatible types";
				mBooleanAbstraction.put(targetVar, value);

			}
			// else: variables of unsupported types are assumed to be \top all the time
			assert mVariables.contains(targetVar) && mVariables.contains(sourceVar) : "unknown variable in assignment: "
					+ targetVar + " := " + sourceVar;
		}
	}

	/**
	 ** Updates this abstract state according to {@code targetVar := sourceVar}.
	 * <p>
	 * Modifies this state in-place.
	 *
	 * @param targetVar
	 *            Variable to be updated
	 * @param sourceVar
	 *            Variable to copy values from
	 */
	protected void copyVar(final IProgramVarOrConst targetVar, final IProgramVarOrConst sourceVar) {
		copyVars(Collections.singletonList(new Pair<>(targetVar, sourceVar)));
	}

	/**
	 * Assigns a boolean variable a value.
	 *
	 * @param var
	 *            Variable to be updated
	 * @param value
	 *            New value of the variable
	 */
	protected void assignBooleanVar(final IProgramVarOrConst var, final BoolValue value) {
		assert mBooleanAbstraction.containsKey(var) : "unknown variable in boolean assignment: " + var;
		assert assertNotBottomBeforeAssign();
		mIsBottom = TVBool.UNCHECKED;
		mBooleanAbstraction.put(var, value);
	}

	/**
	 * Assumes a boolean variable to have a certain value. The resulting value is the intersection of the old and the
	 * assumed value.
	 *
	 * @param var
	 *            Variable to be updated
	 * @param value
	 *            Assumed value of the variable
	 */
	protected void assumeBooleanVar(final IProgramVarOrConst var, final BoolValue value) {
		assert assertNotBottomBeforeAssign();
		mIsBottom = TVBool.UNCHECKED;
		mBooleanAbstraction.put(var, mBooleanAbstraction.get(var).intersect(value));
	}

	/**
	 * Obtains the boolean value for a given program var.
	 *
	 * @param var
	 *            The var to obtain the value for.
	 * @return The corresponding {@link BoolValue} representing the boolean value.
	 */
	protected BoolValue getBoolValue(final IProgramVarOrConst var) {
		if (!SmtSortUtils.isBoolSort(var.getSort().getRealSort())) {
			throw new UnsupportedOperationException("Not a boolean: " + var.getGloballyUniqueId());
		}
		if (!mBooleanAbstraction.containsKey(var)) {
			throw new UnsupportedOperationException(
					"Boolean variable " + var.getGloballyUniqueId() + " not found in this state.");
		}
		return mBooleanAbstraction.get(var);
	}

	/**
	 * The abstract state "bottom" (contains no concrete state) is "un-bottomized" if variables are assigned. This
	 * should not happen (even though it is a safe over-approximation).
	 * <p>
	 * This method does not assert, but should be used inside an assertion.
	 *
	 * @return This abstract state was not bottom
	 */
	private boolean assertNotBottomBeforeAssign() {
		return mIsBottom != TVBool.TRUE && mIsBottom != TVBool.FIXED;
	}

	@Override
	public String toString() {
		return toLogString();
	}

	@Override
	public String toLogString() {
		return mLogStringFunction.apply(this);
	}

	/**
	 * @return The log string function associated with this state.
	 */
	protected Function<OctDomainState, String> getLogStringFunction() {
		return mLogStringFunction;
	}

	/**
	 * Creates a log string, representing this abstract state by printing the full octagon matrix.
	 *
	 * @return Log string with full octagon matrix
	 */
	public String logStringFullMatrix() {
		return logStringMatrix(mNumericAbstraction.toStringFull());
	}

	/**
	 * Creates a multi-line log string, representing this abstract state by printing only the block lower triangular
	 * octagon matrix.
	 *
	 * @return Log string with half octagon matrix
	 */
	public String logStringHalfMatrix() {
		return logStringMatrix(mNumericAbstraction.toStringHalf());
	}

	/**
	 * Creates a multi-line log string, representing this abstract state by printing the octagon matrix (already given
	 * as a log string) and the boolean abstraction.
	 *
	 * @param logStringNumericAbstration
	 *            Log string representation of the octagon matrix
	 * @return Log string (octagon matrix log string + boolean abstraction log string)
	 */
	private String logStringMatrix(final String logStringNumericAbstration) {
		final StringBuilder log = new StringBuilder();
		log.append("\n");
		log.append(logStringNumericAbstration);
		log.append("numeric vars: ").append(mMapNumericVarToIndex);
		log.append("\nnumeric non-int vars: ").append(mNumericNonIntVars);
		log.append("\nboolean abstraction: ").append(mBooleanAbstraction);
		for (final Entry<IProgramVarOrConst, BoolValue> entry : mBooleanAbstraction.entrySet()) {
			log.append(entry.getKey()).append(" = ").append(entry.getValue()).append("\n");
		}
		return log.toString();
	}

	/**
	 * Creates a one-line log string, representing this abstract state by printing interval ranges for all variables and
	 * sums or differences of variables (for instance {@code x-y \in [-5; 3]}).
	 *
	 * @return Log string
	 */
	public String logStringTerm() {
		if (isBottom()) {
			return "false";
		}

		// symbol to relate variables and intervals (x "has a value from interval" [a; b])
		final String in = " = ";
		final String minus = " - ";
		final String plus = " + ";
		// delimiter for interval bounds ( [a "delimiter" b] )
		final String delimiter = "; ";

		// Interval bounds --------------------------------------------------------------
		final StringBuilder intsLog = new StringBuilder("ints: {");
		final StringBuilder realsLog = new StringBuilder("reals: {");
		int reals = 0;
		int ints = 0;
		int top = 0;
		int bot = 0;
		String curDelimiter = "";
		for (final Entry<IProgramVarOrConst, Integer> entry : mMapNumericVarToIndex.entrySet()) {
			final IProgramVarOrConst varName = entry.getKey();
			final OctInterval interval = OctInterval.fromMatrix(mNumericAbstraction, entry.getValue());
			if (interval.isTop()) {
				top++;
				continue;
			} else if (interval.isBottom()) {
				bot++;
			}
			final StringBuilder curLog;
			if (mNumericNonIntVars.contains(varName)) {
				curLog = realsLog;
				reals++;
			} else {
				curLog = intsLog;
				ints++;
			}
			curLog.append(curDelimiter);
			curDelimiter = delimiter;
			curLog.append(varName).append(in).append(interval);
		}

		// Constraints between two different variables ----------------------------------
		final StringBuilder relLog = new StringBuilder("relations: {");
		int rels = 0;
		curDelimiter = "";
		if (mNumericAbstraction.hasNegativeSelfLoop()) {
			relLog.append("\\bot");
			curDelimiter = delimiter;
			rels++;
		}
		for (final Entry<IProgramVarOrConst, Integer> rowEntry : mMapNumericVarToIndex.entrySet()) {
			for (final Entry<IProgramVarOrConst, Integer> colEntry : mMapNumericVarToIndex.entrySet()) {
				final IProgramVarOrConst rowName = rowEntry.getKey();
				final IProgramVarOrConst colName = colEntry.getKey();
				final int row2 = rowEntry.getValue() * 2;
				final int col2 = colEntry.getValue() * 2;

				if (row2 <= col2) {
					// skip block upper triangular part (is coherent/redundant)
					// skip diagonal blocks (already logged, see above)
					continue;
				}

				final OctInterval sumInterval =
						new OctInterval(mNumericAbstraction.get(row2, col2 + 1).negateIfNotInfinity(),
								mNumericAbstraction.get(row2 + 1, col2));
				final OctInterval colMinusRowInterval =
						new OctInterval(mNumericAbstraction.get(row2 + 1, col2 + 1).negateIfNotInfinity(),
								mNumericAbstraction.get(row2, col2));

				if (!sumInterval.isTop()) {
					relLog.append(curDelimiter);
					curDelimiter = delimiter;
					relLog.append(colName).append(plus).append(rowName).append(in).append(sumInterval);
					rels++;
				}

				if (!colMinusRowInterval.isTop()) {
					relLog.append(curDelimiter);
					curDelimiter = delimiter;
					relLog.append(colName).append(minus).append(rowName).append(in).append(colMinusRowInterval);
					rels++;
				}
			}
		}

		final StringBuilder log = new StringBuilder("{");
		if (ints > 0) {
			log.append(intsLog).append("}, ");
		}
		if (reals > 0) {
			log.append(realsLog).append("}, ");
		}
		if (top > 0) {
			log.append(top).append(" vars top, ");
		}
		if (bot > 0) {
			log.append(bot).append(" vars bot, ");
		}
		if (rels > 0) {
			log.append(relLog).append("}, ");
		}

		if (!mBooleanAbstraction.isEmpty()) {
			log.append("bools: ").append(mBooleanAbstraction);
		}
		log.append("}");

		return log.toString();
	}

	@Override
	public OctDomainState compact() {
		return removeVariables(topVariables());
	}

	private Collection<IProgramVarOrConst> topVariables() {
		final ArrayList<IProgramVarOrConst> topVariables = new ArrayList<>();
		// find boolean top variables
		for (final Map.Entry<IProgramVarOrConst, BoolValue> boolVarToValue : mBooleanAbstraction.entrySet()) {
			if (boolVarToValue.getValue() == BoolValue.TOP) {
				topVariables.add(boolVarToValue.getKey());
			}
		}
		// find numeric top variables
		final Set<Integer> varIndicesWithConstraints = mNumericAbstraction.variablesWithConstraints();
		for (final Map.Entry<IProgramVarOrConst, Integer> numVarToIndex : mMapNumericVarToIndex.entrySet()) {
			if (!varIndicesWithConstraints.contains(numVarToIndex.getValue())) {
				topVariables.add(numVarToIndex.getKey());
			}
		}
		return topVariables;
	}

	/**
	 * @return A fresh {@link OctDomainState} which is set to bottom.
	 */
	protected OctDomainState createFreshBottomState() {
		return createFreshState(mLogStringFunction, true);
	}
}
