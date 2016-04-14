/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.function.BiFunction;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.BoogieUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.BidirectionalMap;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

/**
 * Octagon abstract state,
 * based on A. Miné's "The octagon abstract domain" (https://www-apr.lip6.fr/~mine/publi/article-mine-ast01.pdf).
 * 
 * Octagons are a weakly relational abstract domain and store constraints of the form "±x ± y ≤ c"
 * for numerical (ints and reals) variables x, y and a constant c.
 * Boolean variables are stored separately, using the non-relation powerset domain.
 * Other types (bit-vectors for instance) are not supported.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class OctDomainState implements IAbstractState<OctDomainState, CodeBlock, IBoogieVar> {

	/** Counter for created objects. Used to set {@link #mId}. */
	private static int sId = 0;

	/** A human-readable hash code, unique for each object. */
	private final int mId;

	/** Function used to generate log strings. */
	private final Function<OctDomainState, String> mLogStringFunction;
	
	/** Map of variable names to their {@link IBoogieVar}. */
	private Map<String, IBoogieVar> mMapVarToBoogieVar;
	
	/**
	 * Map of numerical variable (ints and reals) names to the index of the corresponding block row/column in the
	 * octagon matrix {@link #mNumericAbstraction}. Block row/column i contains the rows/columns 2i and 2i+1.
	 */
	private Map<String, Integer> mMapNumericVarToIndex;
	
	/** Names of real-valued variables. */
	private Set<String> mNumericNonIntVars;
	
	/** Abstract state for numeric variables (ints and reals). This is the actual octagon. */
	private OctMatrix mNumericAbstraction;
	
	/**
	 * Abstract state for boolean variables. This is a non-relational powerset domain
	 * and maps each boolean variable (name) to the set of values the variable can assume.
	 */
	private Map<String, BoolValue> mBooleanAbstraction;

	/**
	 * The abstract state "bottom" (contains no concrete state) is "un-bottomized" if variables are assigned.
	 * This should not happen (even though it is a safe over-approximation).
	 * <p>
	 * This method does not assert, but should be used inside an assertion.
	 * 
	 * @return This abstract state was not bottom
	 */
	private boolean assertNotBottomBeforeAssign() {
		return !isBottom();
	};

	/**
	 * Creates a new, un-initialized abstract state. <b>Most attributes are not initialized and must be set by hand.</b>
	 * 
	 * @param logStringFunction Function to be used for creating log strings of this abstract state.
	 */
	private OctDomainState(final Function<OctDomainState, String> logStringFunction) {
		mLogStringFunction = logStringFunction;
		mId = sId++;
	}

	/**
	 * Creates a new abstract state without any variables.
	 * 
	 * @param logStringFunction Function to be used for creating log strings of this abstract state.
	 * @return Oct
	 */
	public static OctDomainState createFreshState(final Function<OctDomainState, String> logStringFunction) {
		OctDomainState s = new OctDomainState(logStringFunction);
		s.mMapVarToBoogieVar = new HashMap<>();
		s.mMapNumericVarToIndex = new HashMap<>();
		s.mNumericNonIntVars = new HashSet<>();
		s.mNumericAbstraction = OctMatrix.NEW;
		s.mBooleanAbstraction = new HashMap<>();
		return s;
	}

	public OctDomainState deepCopy() {
		OctDomainState s = new OctDomainState(mLogStringFunction);
		s.mMapVarToBoogieVar = new HashMap<>(mMapVarToBoogieVar);
		s.mMapNumericVarToIndex = new HashMap<>(mMapNumericVarToIndex);
		s.mNumericNonIntVars = new HashSet<>(mNumericNonIntVars);
		s.mNumericAbstraction = mNumericAbstraction.copy();
		s.mBooleanAbstraction = new HashMap<>(mBooleanAbstraction);
		return s;
	}

	/**
	 * Creates a shallow copy of this OctagonDomainState. Use the {@code unref}&hellip; methods to deep copy single
	 * fields before modifying them.
	 *
	 * @return shallow copy
	 *
	 * @see #unrefOtherMapVarToBoogieVar(OctDomainState)
	 * @see #unrefOtherMapNumericVarToIndex(OctDomainState)
	 * @see #unrefOtherNumericNonIntVars(OctDomainState)
	 * @see #unrefOtherNumericAbstraction(OctDomainState)
	 * @see #unrefOtherBooleanAbstraction(OctDomainState)
	 */
	private OctDomainState shallowCopy() {
		OctDomainState s = new OctDomainState(mLogStringFunction);
		s.mMapVarToBoogieVar = mMapVarToBoogieVar;
		s.mMapNumericVarToIndex = mMapNumericVarToIndex;
		s.mNumericNonIntVars = mNumericNonIntVars;
		s.mNumericAbstraction = mNumericAbstraction;
		s.mBooleanAbstraction = mBooleanAbstraction;
		return s;
	}

	private void unrefOtherMapVarToBoogieVar(final OctDomainState other) {
		if (other.mMapVarToBoogieVar == mMapVarToBoogieVar) {
			other.mMapVarToBoogieVar = new HashMap<>(mMapVarToBoogieVar);
		}
	}

	private void unrefOtherMapNumericVarToIndex(final OctDomainState other) {
		if (other.mMapNumericVarToIndex == mMapNumericVarToIndex) {
			other.mMapNumericVarToIndex = new HashMap<>(mMapNumericVarToIndex);
		}
	}

	private void unrefOtherNumericNonIntVars(final OctDomainState other) {
		if (other.mNumericNonIntVars == mNumericNonIntVars) {
			other.mNumericNonIntVars = new HashSet<>(mNumericNonIntVars);
		}
	}

	// currently unused
	// private void unrefOtherNumericAbstraction(OctDomainState other) {
	// if (other.mNumericAbstraction == mNumericAbstraction) {
	// other.mNumericAbstraction = mNumericAbstraction.copy();
	// }
	// }

	private void unrefOtherBooleanAbstraction(final OctDomainState other) {
		if (other.mBooleanAbstraction == mBooleanAbstraction) {
			other.mBooleanAbstraction = new HashMap<>(mBooleanAbstraction);
		}
	}

	@Override
	public Map<String, IBoogieVar> getVariables() {
		return Collections.unmodifiableMap(mMapVarToBoogieVar);
	}

	@Override
	public OctDomainState addVariable(final String name, final IBoogieVar variable) {
		return addVariables(Collections.singletonMap(name, variable));
	}

	@Override
	public OctDomainState removeVariable(final String name, final IBoogieVar variable) {
		return removeVariables(Collections.singletonMap(name, variable));
	}

	// TODO document: Returned state is a shallow copy. Modifications of returned state may also effect this state!
	@Override
	public OctDomainState addVariables(final Map<String, IBoogieVar> variables) {
		// variables = new TreeMap<>(variables); // fixed iteration order -- essential for fast isEqualTo
		// ... probably no speedup. HashSets should iterate in the same order when adding the very same variables.

		final OctDomainState newState = shallowCopy();
		for (Map.Entry<String, IBoogieVar> entry : variables.entrySet()) {
			unrefOtherMapVarToBoogieVar(newState);
			final String varName = entry.getKey();
			final IBoogieVar newBoogieVar = entry.getValue();
			final IBoogieVar oldBoogieVar = newState.mMapVarToBoogieVar.put(varName, newBoogieVar);
			if (oldBoogieVar != null) {
				throw new IllegalArgumentException("Variable name already in use: " + varName);
			}
			IType type = newBoogieVar.getIType();
			if (TypeUtil.isNumeric(type)) {
				unrefOtherMapNumericVarToIndex(newState);
				newState.mMapNumericVarToIndex.put(varName, newState.mMapNumericVarToIndex.size());
				if (TypeUtil.isNumericNonInt(type)) {
					unrefOtherNumericNonIntVars(newState);
					newState.mNumericNonIntVars.add(varName);
				}
			} else if (TypeUtil.isBoolean(type)) {
				unrefOtherBooleanAbstraction(newState);
				newState.mBooleanAbstraction.put(varName, BoolValue.TOP);
			}
			// else: variable has unsupported type and is assumed to be \top at all times
		}
		newState.mNumericAbstraction = mNumericAbstraction
				.addVariables(newState.mMapNumericVarToIndex.size() - mMapNumericVarToIndex.size());
		return newState;
	}

	// TODO document: Returned state is a shallow copy. Do not modify!
	@Override
	public OctDomainState removeVariables(final Map<String, IBoogieVar> variables) {

		final OctDomainState newState = shallowCopy();
		final Set<Integer> indexRemovedNumericVars = new HashSet<>();
		for (String name : variables.keySet()) {
			unrefOtherMapVarToBoogieVar(newState);
			newState.mMapVarToBoogieVar.remove(name);
			if (newState.mMapNumericVarToIndex.containsKey(name)) {
				unrefOtherMapNumericVarToIndex(newState);
				int i = newState.mMapNumericVarToIndex.remove(name);
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
			defragmentMap(newState.mMapNumericVarToIndex); // already unref'd
		}
		return newState;
	}

	private static <T> void defragmentMap(final Map<T, Integer> map) {
		final TreeMap<Integer, T> reversedMapSortedAscending = new TreeMap<Integer, T>();
		for (Map.Entry<T, Integer> entry : map.entrySet()) {
			reversedMapSortedAscending.put(entry.getValue(), entry.getKey());
		}
		map.clear();
		int newIndex = 0;
		for (Map.Entry<Integer, T> entry : reversedMapSortedAscending.entrySet()) {
			map.put(entry.getValue(), newIndex);
			++newIndex;
		}
	}

	@Override
	public IBoogieVar getVariableDeclarationType(final String name) {
		return mMapVarToBoogieVar.get(name);
	}

	@Override
	public boolean containsVariable(final String name) {
		return mMapVarToBoogieVar.containsKey(name);
	}

	@Override
	public boolean isEmpty() {
		return mMapVarToBoogieVar.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return isBooleanAbstractionBottom() || isNumericAbstractionBottom();
	}

	private boolean isNumericAbstractionBottom() {
		return cachedSelectiveClosure().hasNegativeSelfLoop();
	}

	private boolean isBooleanAbstractionBottom() {
		return mBooleanAbstraction.containsValue(BoolValue.BOT);
	}

	// TODO document
	// - returns original cache. Do not modify in-place!
	private OctMatrix cachedSelectiveClosure() {
		if (isNumericAbstractionIntegral()) {
			return mNumericAbstraction.cachedTightClosure();
		} else {
			return mNumericAbstraction.cachedStrongClosure();
		}
	}

	private OctMatrix bestAvailableClosure() {
		if (isNumericAbstractionIntegral() && mNumericAbstraction.hasCachedTightClosure()) {
			return mNumericAbstraction.cachedTightClosure();
		} else if (mNumericAbstraction.hasCachedStrongClosure()) {
			return mNumericAbstraction.cachedStrongClosure();
		}
		return mNumericAbstraction;
	}

	private boolean isNumericAbstractionIntegral() {
		return mNumericNonIntVars.isEmpty();
	}

	@Override
	public boolean isEqualTo(OctDomainState other) {
		if (other == null) {
			return false;
		} else if (other == this) {
			return true;
		} else {
			boolean isEqual = mMapVarToBoogieVar.equals(other.mMapVarToBoogieVar)
					&& mBooleanAbstraction.equals(other.mBooleanAbstraction) && numericAbstractionIsEqualTo(other);
			return isEqual;
		}
	}

	@Override
	public SubsetResult isSubsetOf(final OctDomainState other) {
		assert mMapVarToBoogieVar.equals(other.mMapVarToBoogieVar);
		for (Map.Entry<String, BoolValue> thisEntry : mBooleanAbstraction.entrySet()) {
			final BoolValue thisVal = thisEntry.getValue();
			final BoolValue otherVal = other.mBooleanAbstraction.get(thisEntry.getKey());
			if (!thisVal.isSubsetEqual(otherVal)) {
				return SubsetResult.NONE;
			}
		}
		if (!cachedSelectiveClosure().elementwiseRelation(other.cachedSelectiveClosure(),
				(thisVal, otherVal) -> thisVal.compareTo(otherVal) <= 0)) {
			return SubsetResult.NONE;
		}
		return SubsetResult.NON_STRICT;
	}

	@Override
	public int hashCode() {
		return mId;
	}

	// TODO document
	// - call only when same variables are stored
	private boolean numericAbstractionIsEqualTo(final OctDomainState other) {
		assert mMapNumericVarToIndex.keySet().equals(other.mMapNumericVarToIndex.keySet());
		boolean permutated = false;
		int[] mapThisVarIndexToOtherVarIndex = new int[mNumericAbstraction.variables()];
		for (Map.Entry<String, Integer> entry : mMapNumericVarToIndex.entrySet()) {
			String var = entry.getKey();
			int thisVarIndex = entry.getValue();
			int otherVarIndex = other.mMapNumericVarToIndex.get(var);
			if (thisVarIndex != otherVarIndex) {
				permutated = true;
			}
			mapThisVarIndexToOtherVarIndex[thisVarIndex] = otherVarIndex;
		}
		OctMatrix thisClosure = cachedSelectiveClosure();
		OctMatrix otherClosure = other.cachedSelectiveClosure();
		boolean thisIsBottom = thisClosure.hasNegativeSelfLoop();
		boolean otherIsBottom = otherClosure.hasNegativeSelfLoop();
		if (thisIsBottom != otherIsBottom) {
			return false;
		} else if (thisIsBottom) { // && otherIsBottom
			return true;
		} else if (permutated) {
			return thisClosure.isEqualToPermutation(otherClosure, mapThisVarIndexToOtherVarIndex);
		} else {
			return thisClosure.isEqualTo(otherClosure);
		}
	}

	// TODO document: Returned state is a shallow copy. Do not modify!
	public OctDomainState meet(final OctDomainState other) {
		final OctMatrix numResult = OctMatrix.min(bestAvailableClosure(), other.bestAvailableClosure());
		return operation(other, BoolValue::intersect, numResult);
	}

	// TODO document: Returned state is a shallow copy. Do not modify!
	public OctDomainState join(final OctDomainState other) {
		final OctMatrix numResult = OctMatrix.max(bestAvailableClosure(), other.bestAvailableClosure());
		return operation(other, BoolValue::union, numResult);
	}

	// TODO document: Returned state is a shallow copy. Do not modify!
	public OctDomainState widen(final OctDomainState other, final BiFunction<OctMatrix, OctMatrix, OctMatrix> widenOp) {
		// left argument of widening operation must not be closed (or widening may not stabilize)!
		final OctMatrix numResult = widenOp.apply(mNumericAbstraction, other.bestAvailableClosure());
		return operation(other, BoolValue::union, numResult);
	}

	// TODO document: Returned state is a shallow copy. Do not modify!
	// operation only on bools. Operation on numeric abstraction has to be applied manually.
	private OctDomainState operation(final OctDomainState other,
			final BiFunction<BoolValue, BoolValue, BoolValue> booleanOperation,
			final OctMatrix numericAbstractionResult) {
		final OctDomainState result = shallowCopy();
		for (Map.Entry<String, BoolValue> entry : mBooleanAbstraction.entrySet()) {
			final String name = entry.getKey();
			final BoolValue oldValue = entry.getValue();
			final BoolValue newValue = booleanOperation.apply(oldValue, other.mBooleanAbstraction.get(name));
			if (!oldValue.equals(newValue)) {
				unrefOtherBooleanAbstraction(result);
				result.mBooleanAbstraction.put(name, newValue);
			}
		}
		result.mNumericAbstraction = numericAbstractionResult;
		return result;
	}

	@Override
	public Term getTerm(final Script script, final Boogie2SMT bpl2smt) {
		if (isBottom()) {
			return script.term("false");
		}

		final List<Term> terms = new ArrayList<Term>();
		terms.addAll(getTermNumericAbstraction(script, bpl2smt));
		terms.addAll(getTermBooleanAbstraction(script, bpl2smt));
		return Util.and(script, terms.toArray(new Term[terms.size()]));
	}

	private List<Term> getTermNumericAbstraction(final Script script, final Boogie2SMT bpl2smt) {
		final Term[] mapIndexToTerm = new Term[mMapNumericVarToIndex.size()];
		for (final Entry<String, Integer> entry : mMapNumericVarToIndex.entrySet()) {
			final Term termVar = getTermVar(entry.getKey());
			mapIndexToTerm[entry.getValue()] = termVar;
		}
		return cachedSelectiveClosure().getTerm(script, mapIndexToTerm);
	}

	private List<Term> getTermBooleanAbstraction(final Script script, final Boogie2SMT bpl2smt) {
		final List<Term> rtr = new ArrayList<Term>(mBooleanAbstraction.size());
		for (final Entry<String, BoolValue> entry : mBooleanAbstraction.entrySet()) {
			final Term termVar = getTermVar(entry.getKey());
			final Sort sort = termVar.getSort().getRealSort();
			final Term newTerm = entry.getValue().getTerm(script, sort, termVar);
			rtr.add(newTerm);
		}
		return rtr;
	}

	private Term getTermVar(final String varName) {
		final IBoogieVar var = mMapVarToBoogieVar.get(varName);
		if (var instanceof BoogieVar) {
			return ((BoogieVar) var).getTermVariable();
		} else if (var instanceof BoogieConst) {
			return ((BoogieConst) var).getDefaultConstant();
		}
		return null;
	}

	// TODO test
	// TODO document: Returned state is a shallow copy. Do not modify!
	@Override
	public OctDomainState patch(final OctDomainState dominator) {
		assertNotBottomBeforeAssign();

		final OctDomainState patchedState = shallowCopy();
		final BidirectionalMap<Integer, Integer> mapTargetVarToSourceVar = new BidirectionalMap<>();
		final SortedMap<Integer, String> mapDominatorIndicesOfNewNumericVars = new TreeMap<>();

		for (Map.Entry<String, IBoogieVar> entry : dominator.mMapVarToBoogieVar.entrySet()) {
			final String newVar = entry.getKey();
			final IBoogieVar newBoogieVar = entry.getValue();
			unrefOtherMapVarToBoogieVar(patchedState);
			final IBoogieVar oldBoogieVar = patchedState.mMapVarToBoogieVar.put(newVar, newBoogieVar);
			assert oldBoogieVar == null
					|| mMapVarToBoogieVar.get(newVar) == newBoogieVar : "Patch caused name-collision: " + newVar;
			final IType type = newBoogieVar.getIType();
			if (TypeUtil.isNumeric(type)) {
				int sourceVar = dominator.mMapNumericVarToIndex.get(newVar);
				if (oldBoogieVar == null) {
					mapDominatorIndicesOfNewNumericVars.put(sourceVar, newVar);
					if (TypeUtil.isNumericNonInt(type)) {
						unrefOtherNumericNonIntVars(patchedState);
						patchedState.mNumericNonIntVars.add(newVar);
					}
				} else {
					int targetVar = patchedState.mMapNumericVarToIndex.get(newVar);
					mapTargetVarToSourceVar.put(targetVar, sourceVar);
				}
			} else if (TypeUtil.isBoolean(type)) {
				unrefOtherBooleanAbstraction(patchedState);
				patchedState.mBooleanAbstraction.put(newVar, dominator.mBooleanAbstraction.get(newVar));
			}
			// else: variable has unsupported type and is assumed to be \top
		}
		for (final String var : mapDominatorIndicesOfNewNumericVars.values()) {
			unrefOtherMapNumericVarToIndex(patchedState);
			patchedState.mMapNumericVarToIndex.put(var, patchedState.mMapNumericVarToIndex.size());
		}
		patchedState.mNumericAbstraction = cachedSelectiveClosure().appendSelection(dominator.mNumericAbstraction,
				mapDominatorIndicesOfNewNumericVars.keySet());
		patchedState.mNumericAbstraction.copySelection(dominator.mNumericAbstraction, mapTargetVarToSourceVar);
		return patchedState;
	}

	// TODO document: Returned state is a shallow copy. Modifications on return value may also modify this
	// OctDomainState!
	public OctDomainState copyValuesOnScopeChange(final OctDomainState source,
			final List<Pair<String, String>> mapTargetToSource) {

		assert assertNotBottomBeforeAssign();

		// TODO closure in advance to reduce information loss

		final BidirectionalMap<Integer, Integer> mapNumericTargetToSource = new BidirectionalMap<>();
		final List<Pair<String, String>> mapBooleanTargetToSource = new ArrayList<>(mapTargetToSource.size());

		// shared (=global) numeric variables (copy to keep relations between globals and in/out-parameters)
		for (final String var : sharedGlobalVars(source)) {
			final Integer targetIndex = mMapNumericVarToIndex.get(var);
			if (targetIndex != null) {
				final Integer sourceIndex = source.mMapNumericVarToIndex.get(var);
				assert sourceIndex != null : "shared variables are not really shared";
				mapNumericTargetToSource.put(targetIndex, sourceIndex);
			}
			// do not copy shared (=global) booleans (again). Already done by patch(...).
		}

		// in/out-parameters (from one scope) to locals (from another scope)
		for (final Pair<String, String> assignmentPair : mapTargetToSource) {
			final String targetVar = assignmentPair.getFirst();
			final String sourceVar = assignmentPair.getSecond();
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
		if (!mapNumericTargetToSource.isEmpty()) {
			newState.mNumericAbstraction = cachedSelectiveClosure().copy();
			newState.mNumericAbstraction.copySelection(source.mNumericAbstraction, mapNumericTargetToSource);
		}
		if (!mapBooleanTargetToSource.isEmpty()) {
			unrefOtherBooleanAbstraction(newState);
			for (final Pair<String, String> entry : mapBooleanTargetToSource) {
				final String targetVar = entry.getFirst();
				final String sourceVar = entry.getSecond();
				final BoolValue sourceValue = source.mBooleanAbstraction.get(sourceVar);
				newState.mBooleanAbstraction.put(targetVar, sourceValue);
			}
		}
		return newState;
	}

	// /**
	// * Finds the shared global variables and constants between {@code this} and an {@code other} abstract domain
	// state.
	// * Found global variables and constants are added to existing collections.
	// * <p>
	// * Shared variables/constants are the exact same variables/constants.
	// * Different variables/constants with equal names or even equal types are not shared.
	// *
	// * @param other abstract domain state
	// * @param sharedGlobals collection where the shared global variables are added or {@code null}
	// * @param sharedConstants collection where the shared constants are added or {@code null}
	// */
	// public void sharedNumericGlobals(OctagonDomainState other,
	// Collection<String> sharedGlobals, Collection<String> sharedConstants) {
	// for (Map.Entry<String, IBoogieVar> var : sharedVars(other)) {
	// IBoogieVar ibv = var.getValue();
	// if (isNumeric(ibv.getIType())) {
	// if (sharedConstants != null && ibv instanceof BoogieConst) {
	// sharedConstants.add(var.getKey());
	// } else if (sharedGlobals != null && ibv instanceof BoogieVar && ((BoogieVar) ibv).isGlobal()) {
	// sharedGlobals.add(var.getKey());
	// }
	// }
	// }
	// }

	public Set<String> sharedGlobalVars(final OctDomainState other) {
		final Set<String> sharedVars = new HashSet<>();
		final Set<Map.Entry<String, IBoogieVar>> otherEntrySet = other.mMapVarToBoogieVar.entrySet();
		for (final Map.Entry<String, IBoogieVar> entry : mMapVarToBoogieVar.entrySet()) {
			if (BoogieUtil.isGlobal(entry.getValue()) && otherEntrySet.contains(entry)) {
				sharedVars.add(entry.getKey());
			}
		}
		return sharedVars;
	}

	protected void havocVar(final String var) {
		havocVars(Collections.singleton(var));
	}

	// TODO Only calculate closure if necessary. Some vars may have no constraints to other vars => no closure
	protected void havocVars(final Collection<String> vars) {
		assert assertNotBottomBeforeAssign();
		final Set<Integer> numVarIndices = new HashSet<>();
		for (final String var : vars) {
			Integer numVarIndex = mMapNumericVarToIndex.get(var);
			if (numVarIndex != null) {
				numVarIndices.add(numVarIndex);
			} else if (mBooleanAbstraction.containsKey(var)) {
				mBooleanAbstraction.put(var, BoolValue.TOP);
			}
			// else: variables of unsupported types are assumed to be \top all the time
			assert mMapVarToBoogieVar.containsKey(var) : "unknown variable in havoc: " + var;
		}
		if (!numVarIndices.isEmpty()) {
			mNumericAbstraction = cachedSelectiveClosure().copy();
			numVarIndices.forEach(v -> mNumericAbstraction.havocVar(v));
		}
	}

	// v := v + c;
	protected void incrementNumericVar(final String targetVar, final OctValue addConstant) {
		assert assertNotBottomBeforeAssign();
		mNumericAbstraction.incrementVar(numVarIndex(targetVar), addConstant);
	}

	protected void negateNumericVar(final String targetVar) {
		assert assertNotBottomBeforeAssign();
		mNumericAbstraction.negateVar(numVarIndex(targetVar));
	}

	protected void assignNumericVarConstant(final String targetVar, final OctValue constant) {
		assert assertNotBottomBeforeAssign();
		mNumericAbstraction = cachedSelectiveClosure().copy();
		mNumericAbstraction.assignVarConstant(numVarIndex(targetVar), constant);
	}

	// min <= var <= max
	protected void assignNumericVarInterval(final String targetVar, final OctInterval interval) {
		assert assertNotBottomBeforeAssign();
		mNumericAbstraction = cachedSelectiveClosure().copy();
		mNumericAbstraction.assignVarInterval(numVarIndex(targetVar), interval.getMin(), interval.getMax());
	}

	protected void assumeNumericVarConstant(final String targetVar, final OctValue constant) {
		mNumericAbstraction.assumeVarConstant(numVarIndex(targetVar), constant);
	}

	// min <= var <= max
	protected void assumeNumericVarInterval(final String targetVar, final OctValue min, final OctValue max) {
		mNumericAbstraction.assumeVarInterval(numVarIndex(targetVar), min, max);
	}

	// var1 + var2 <= zero
	protected void assumeNumericVarRelationLeConstant(final String var1, final boolean var1Negate,
			final String var2, final boolean var2Negate, final OctValue constant) {
		mNumericAbstraction.assumeVarRelationLeConstant(numVarIndex(var1), var1Negate,numVarIndex(var2), var2Negate,
				constant);
	}

	public OctInterval projectToInterval(final String numericVar) {
		return OctInterval.fromMatrix(cachedSelectiveClosure(), numVarIndex(numericVar));
	}

	public OctInterval projectToInterval(final AffineExpression.TwoVarForm tvf) {
		int iVar1 = mMapNumericVarToIndex.get(tvf.var1) * 2;
		int iVar2Inv = mMapNumericVarToIndex.get(tvf.var2) * 2 + 1; // inverted form, because x-(-y) = x+y
		if (tvf.negVar1) {
			iVar1 = iVar1 + 1;
		}
		if (tvf.negVar2) {
			iVar2Inv = iVar2Inv - 1;
		}
		final OctMatrix m = cachedSelectiveClosure();
		// var1 - (-var2) <= c equivalent var1 + var2 <= c
		OctValue max = m.get(iVar2Inv, iVar1);
		// (-var1) - var2 <= c equivalent -c <= var1 + var2
		OctValue min = m.get(iVar2Inv ^ 1, iVar1 ^ 1).negateIfNotInfinity();
		if (tvf.constant.signum() != 0) {
			max = max.add(tvf.constant);
			min = min.add(tvf.constant);
		}
		// TODO negate min
		return new OctInterval(min, max);
	}

	private int numVarIndex(final String var) {
		final Integer index = mMapNumericVarToIndex.get(var);
		assert index != null : "Not a numeric variable: " + var;
		return index;
	}

	// targetVar1, targetVar2, ... := sourceVar1, sourceVar2, ...
	protected void copyVars(final List<Pair<String, String>> mapTargetVarToSourceVar) {

		assert assertNotBottomBeforeAssign();

		boolean usedClosure = false;

		for (final Pair<String, String> entry : mapTargetVarToSourceVar) {
			final String targetVar = entry.getFirst();
			final String sourceVar = entry.getSecond();

			final Integer targetIndex = mMapNumericVarToIndex.get(targetVar);
			if (targetIndex != null) {
				if (!usedClosure) {
					mNumericAbstraction = cachedSelectiveClosure().copy();
					usedClosure = true;
				}
				final Integer sourceIndex = mMapNumericVarToIndex.get(sourceVar);
				assert sourceIndex != null : "Incompatible types";
				mNumericAbstraction.assignVarCopy(targetIndex, sourceIndex);

			} else if (mBooleanAbstraction.containsKey(targetVar)) {
				BoolValue value = mBooleanAbstraction.get(sourceVar);
				assert value != null : "Incompatible types";
				mBooleanAbstraction.put(targetVar, value);

			}
			// else: variables of unsupported types are assumed to be \top all the time
			assert mMapVarToBoogieVar.containsKey(targetVar)
					&& mMapVarToBoogieVar.containsKey(sourceVar) : "unknown variable in assignment: " + targetVar
							+ " := " + sourceVar;
		}
	}

	// targetVar := sourceVar
	// TODO rename to: assignVarCopy
	protected void copyVar(final String targetVar, final String sourceVar) {
		copyVars(Collections.singletonList(new Pair<>(targetVar, sourceVar)));
	}

	protected void assignBooleanVar(final String var, final BoolValue value) {
		assert mBooleanAbstraction.containsKey(var) : "unknown variable in boolean assignment: " + var;
		assert assertNotBottomBeforeAssign();
		mBooleanAbstraction.put(var, value);
	}

	protected void assumeBooleanVar(final String var, final BoolValue value) {
		mBooleanAbstraction.put(var, mBooleanAbstraction.get(var).intersect(value));
	}

	@Override
	public String toString() {
		// return toLogString();
		return logStringHalfMatrix();
	}

	@Override
	public String toLogString() {
		return mLogStringFunction.apply(this);
	}

	public String logStringFullMatrix() {
		return logStringMatrix(mNumericAbstraction.toStringFull());
	}

	public String logStringHalfMatrix() {
		return logStringMatrix(mNumericAbstraction.toStringHalf());
	}

	private String logStringMatrix(String logStringNumericAbstration) {
		StringBuilder log = new StringBuilder();
		log.append("\n");

		// TODO remove (only for debugging)
		log.append("#").append(mId);

		log.append(logStringNumericAbstration);

		log.append("numeric vars: ").append(mMapNumericVarToIndex);
		log.append("\nnumeric non-int vars: ").append(mNumericNonIntVars);
		log.append("\nboolean abstraction: ").append(mBooleanAbstraction);

		// for (Map.Entry<String, BoolValue> entry : mBooleanAbstraction.entrySet()) {
		// log.append(entry.getKey()).append(" = ").append(entry.getValue()).append("\n");
		// }

		// TODO remove
		log.append("\n#END\n");

		// TODO remove
		log.append(logStringTerm()).append("\n");

		return log.toString();
	}

	public String logStringTerm() {
		final String in = " = ";
		final String minus = " - ";
		final String plus = " + ";
		final String delimiter = "; ";

		// Interval bounds --------------------------------------------------------------
		final StringBuilder intsLog = new StringBuilder("ints: {");
		final StringBuilder realsLog = new StringBuilder("reals: {");
		int reals = 0;
		int ints = 0;
		String curDelimiter = "";
		for (final Entry<String, Integer> entry : mMapNumericVarToIndex.entrySet()) {
			final String varName = entry.getKey();
			final OctInterval interval = OctInterval.fromMatrix(mNumericAbstraction, entry.getValue());

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
		for (final Entry<String, Integer> rowEntry : mMapNumericVarToIndex.entrySet()) {
			for (final Entry<String, Integer> colEntry : mMapNumericVarToIndex.entrySet()) {
				final String rowName = rowEntry.getKey();
				final String colName = colEntry.getKey();
				final int row2 = rowEntry.getValue() * 2;
				final int col2 = colEntry.getValue() * 2;

				if (row2 <= col2) {
					// skip block upper triangular part (is coherent/redundant)
					// skip diagonal blocks (already logged, see above)
					continue;
				}

				final OctInterval sumInterval = new OctInterval(
						mNumericAbstraction.get(row2, col2 + 1).negateIfNotInfinity(),
						mNumericAbstraction.get(row2 + 1, col2));
				final OctInterval colMinusRowInterval = new OctInterval(
						mNumericAbstraction.get(row2 + 1, col2 + 1).negateIfNotInfinity(),
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

		final StringBuilder rtr = new StringBuilder("{");
		if (ints > 0) {
			rtr.append(intsLog).append("}, ");
		}
		if (reals > 0) {
			rtr.append(realsLog).append("}, ");
		}
		if (rels > 0) {
			rtr.append(relLog).append("}, ");
		}
		if (!mBooleanAbstraction.isEmpty()) {
			rtr.append("bools: ").append(mBooleanAbstraction);
		}
		rtr.append("}");

		return rtr.toString();
	}

}
