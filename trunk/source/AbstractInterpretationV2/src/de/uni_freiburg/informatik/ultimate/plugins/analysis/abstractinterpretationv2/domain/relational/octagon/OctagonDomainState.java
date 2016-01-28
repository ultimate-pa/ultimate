package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.Map.Entry;
import java.util.function.BiFunction;

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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.BoogieAstUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.BidirectionalMap;

public class OctagonDomainState implements IAbstractState<OctagonDomainState, CodeBlock, IBoogieVar> {
	
	private static int sId;

	/** A human-readable hash code, unique for each object. */
	private final int mId;

	private Map<String, IBoogieVar> mMapVarToBoogieVar;
	private Map<String, Integer> mMapNumericVarToIndex;
	private Set<String> mNumericNonIntVars;
	private OctMatrix mNumericAbstraction;
	private Map<String, BoolValue> mBooleanAbstraction;

	public static OctagonDomainState createFreshState() {
		OctagonDomainState s = new OctagonDomainState();
		s.mMapVarToBoogieVar = new HashMap<>();
		s.mMapNumericVarToIndex = new HashMap<>();
		s.mNumericNonIntVars = new HashSet<>();
		s.mNumericAbstraction = OctMatrix.NEW;
		s.mBooleanAbstraction = new HashMap<>();
		return s;
	}

	private OctagonDomainState() {
		mId = sId++;
	}

	public OctagonDomainState deepCopy() {
		OctagonDomainState s = new OctagonDomainState();
		s.mMapVarToBoogieVar = new HashMap<>(mMapVarToBoogieVar);
		s.mMapNumericVarToIndex = new HashMap<>(mMapNumericVarToIndex);
		s.mNumericNonIntVars = new HashSet<>(mNumericNonIntVars);
		s.mNumericAbstraction = mNumericAbstraction.copy();
		s.mBooleanAbstraction = new HashMap<>(mBooleanAbstraction);
		return s;
	}

	/**
	 * Creates a shallow copy of this OctagonDomainState.
	 * Use the {@code unref}&hellip; methods to deep copy single fields
	 * before modifying them in-place.
	 *
	 * @return shallow copy
	 *
	 * @see #unrefMapVarToBoogieVar(OctagonDomainState)
	 * @see #unrefMapNumericVarToIndex(OctagonDomainState)
	 * @see #unrefNumericNonIntVars(OctagonDomainState)
	 * @see #unrefNumericAbstraction(OctagonDomainState)
	 * @see #unrefBooleanAbstraction(OctagonDomainState)
	 */
	private OctagonDomainState shallowCopy() {
		OctagonDomainState s = new OctagonDomainState();
		s.mMapVarToBoogieVar = mMapVarToBoogieVar;
		s.mMapNumericVarToIndex = mMapNumericVarToIndex;
		s.mNumericNonIntVars = mNumericNonIntVars;
		s.mNumericAbstraction = mNumericAbstraction;
		s.mBooleanAbstraction = mBooleanAbstraction;
		return s;
	}

	private void unrefMapVarToBoogieVar(OctagonDomainState state) {
		if (state.mMapVarToBoogieVar == mMapVarToBoogieVar) {
			state.mMapVarToBoogieVar = new HashMap<>(mMapVarToBoogieVar);
		}
	}

	private void unrefMapNumericVarToIndex(OctagonDomainState state) {
		if (state.mMapNumericVarToIndex == mMapNumericVarToIndex) {
			state.mMapNumericVarToIndex = new HashMap<>(mMapNumericVarToIndex);
		}
	}

	private void unrefNumericNonIntVars(OctagonDomainState state) {
		if (state.mNumericNonIntVars == mNumericNonIntVars) {
			state.mNumericNonIntVars = new HashSet<>(mNumericNonIntVars);
		}
	}

	private void unrefNumericAbstraction(OctagonDomainState state) {
		if (state.mNumericAbstraction == mNumericAbstraction) {
			state.mNumericAbstraction = mNumericAbstraction.copy();
		}
	}

	private void unrefBooleanAbstraction(OctagonDomainState state) {
		if (state.mBooleanAbstraction == mBooleanAbstraction) {
			state.mBooleanAbstraction = new HashMap<>(mBooleanAbstraction);
		}
	}

	@Override
	public Map<String, IBoogieVar> getVariables() {
		return Collections.unmodifiableMap(mMapVarToBoogieVar);
	}

	@Override
	public OctagonDomainState addVariable(String name, IBoogieVar variable) {
		return addVariables(Collections.singletonMap(name, variable));
	}

	@Override
	public OctagonDomainState removeVariable(String name, IBoogieVar variable) {
		return removeVariables(Collections.singletonMap(name, variable));
	}

	@Override
	public OctagonDomainState addVariables(Map<String, IBoogieVar> variables) {
		// variables = new TreeMap<>(variables); // fixed iteration order -- essential for fast isEqualTo
		// ... probably no speedup. HashSets should iterate in the same order when adding the very same variables.
		
		OctagonDomainState newState = shallowCopy();
		newState.mMapVarToBoogieVar = new HashMap<>(mMapVarToBoogieVar);
		for (Map.Entry<String, IBoogieVar> entry : variables.entrySet()) {
			String varName = entry.getKey();
			IBoogieVar newBoogieVar = entry.getValue();
			IBoogieVar oldBoogieVar = newState.mMapVarToBoogieVar.put(varName, newBoogieVar);
			if (oldBoogieVar != null) {
				throw new IllegalArgumentException("Variable name already in use: " + varName);
			}
			IType type = newBoogieVar.getIType();
			if (TypeUtil.isNumeric(type)) {
				unrefMapNumericVarToIndex(newState);
				newState.mMapNumericVarToIndex.put(varName, newState.mMapNumericVarToIndex.size());
				if (TypeUtil.isNumericNonInt(type)) {
					unrefNumericNonIntVars(newState);
					newState.mNumericNonIntVars.add(varName);
				}
			} else if (TypeUtil.isBoolean(type)) {
				unrefBooleanAbstraction(newState);
				newState.mBooleanAbstraction.put(varName, BoolValue.TOP);
			}
			// else: variable has unsupported type and is assumed to be \top at all times
		}
		newState.mNumericAbstraction = mNumericAbstraction
				.addVariables(newState.mMapNumericVarToIndex.size() - mMapNumericVarToIndex.size());
		return newState;
	}

	@Override
	public OctagonDomainState removeVariables(Map<String, IBoogieVar> variables) {
		OctagonDomainState newState = shallowCopy();
		newState.mMapVarToBoogieVar = new HashMap<>(mMapVarToBoogieVar);
		Set<Integer> indexRemovedNumericVars = new HashSet<>();
		for (String name : variables.keySet()) {
			newState.mMapVarToBoogieVar.remove(name);
			if (newState.mMapNumericVarToIndex.containsKey(name)) {
				unrefMapNumericVarToIndex(newState);
				int i = newState.mMapNumericVarToIndex.remove(name);
				indexRemovedNumericVars.add(i);
				if (mNumericNonIntVars.contains(name)) {
					unrefNumericNonIntVars(newState);
					newState.mNumericNonIntVars.remove(name);
				}
			} else if (mBooleanAbstraction.containsKey(name)) {
				unrefBooleanAbstraction(newState);
				newState.mBooleanAbstraction.remove(name);
			}
			// else: variable had an unsupported type => its abstract value (\top) wasn't stored explicitly
			//       or variable was not stored at all => already removed
		}
		if (!indexRemovedNumericVars.isEmpty()) {
			newState.mNumericAbstraction = cachedNormalizedNumericAbstraction().removeVariables(indexRemovedNumericVars);
			defragmentMap(newState.mMapNumericVarToIndex);
		}
		return newState;
	}

	private static <T> void defragmentMap(Map<T, Integer> map) {
		TreeMap<Integer, T> reversedMapSortedAscending = new TreeMap<Integer, T>();
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
	public IBoogieVar getVariableType(String name) {
		return mMapVarToBoogieVar.get(name);
	}

	@Override
	public boolean containsVariable(String name) {
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
		return cachedNormalizedNumericAbstraction().hasNegativeSelfLoop();
	}

	private boolean isBooleanAbstractionBottom() {
		for (BoolValue b : mBooleanAbstraction.values()) {
			if (BoolValue.BOT.equals(b)) {
				return true;
			}
		}
		return false;
	}

	// TODO document: returns original cache. Do not modify in-place!
	private OctMatrix cachedNormalizedNumericAbstraction() {
		if (isNumericAbstractionIntegral()) {
			return mNumericAbstraction.cachedTightClosure();
		} else {
			return mNumericAbstraction.cachedStrongClosure();
		}
	}

	private boolean isNumericAbstractionIntegral() {
		return mNumericNonIntVars.isEmpty();
	}

	@Override
	public boolean isEqualTo(OctagonDomainState other) {
		if (other == null) {
			return false;
		} else if (other == this) {
			return true;
		} else {
			boolean isEqual = mMapVarToBoogieVar.equals(other.mMapVarToBoogieVar)
					&& mBooleanAbstraction.equals(other.mBooleanAbstraction)
					&& numericAbstractionIsEqualTo(other);
			return isEqual;
		}
	}

	@Override
	public int hashCode() {
		return mId;
	}

	// TODO document: call only when same variables are stored
	private boolean numericAbstractionIsEqualTo(OctagonDomainState other) {
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
		OctMatrix thisClosure = cachedNormalizedNumericAbstraction();
		OctMatrix otherClosure = other.cachedNormalizedNumericAbstraction();
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

	public OctagonDomainState meet(OctagonDomainState other) {
		return operation(other, BoolValue::meet, OctMatrix::min);
	}

	public OctagonDomainState join(OctagonDomainState other) {
		return operation(other, BoolValue::join, OctMatrix::max);
	}

	public OctagonDomainState widen(OctagonDomainState other, BiFunction<OctMatrix, OctMatrix, OctMatrix> widenOp) {
		return operation(other, BoolValue::join, widenOp);
	}

	private OctagonDomainState operation(OctagonDomainState other,
			BiFunction<BoolValue, BoolValue, BoolValue> booleanOperation,
			BiFunction<OctMatrix, OctMatrix, OctMatrix> numericOperation) {
		OctagonDomainState result = shallowCopy();
		for (Map.Entry<String, BoolValue> entry : mBooleanAbstraction.entrySet()) {
			String name = entry.getKey();
			BoolValue oldValue = entry.getValue();
			BoolValue newValue = booleanOperation.apply(oldValue, other.mBooleanAbstraction.get(name));
			if (!oldValue.equals(newValue)) {
				unrefBooleanAbstraction(result);
				result.mBooleanAbstraction.put(name, newValue);
			}
		}
		result.mNumericAbstraction = numericOperation.apply(mNumericAbstraction, other.mNumericAbstraction);
		return result;
	}

	@Override
	public Term getTerm(Script script, Boogie2SMT bpl2smt) {
		if (isBottom()) {
			return script.term("false");
		}
		Term n = getTermNumericAbstraction(script, bpl2smt);
		Term b = getTermBooleanAbstraction(script, bpl2smt);
		return Util.and(script, n, b);
	}

	private Term getTermNumericAbstraction(Script script, Boogie2SMT bpl2smt) {
		Term[] mapIndexToTerm = new Term[mMapNumericVarToIndex.size()];
		for (Map.Entry<String, Integer> entry : mMapNumericVarToIndex.entrySet()) {
			Term termVar = getTermVar(entry.getKey());
			mapIndexToTerm[entry.getValue()] = termVar;
		}
		return mNumericAbstraction.getTerm(script, Arrays.asList(mapIndexToTerm));
	}

	private Term getTermBooleanAbstraction(Script script, Boogie2SMT bpl2smt) {
		Term acc = script.term("true");
		for (Entry<String, BoolValue> entry : mBooleanAbstraction.entrySet()) {
			Term termVar = getTermVar(entry.getKey());
			Sort sort = termVar.getSort().getRealSort();
			Term newTerm = entry.getValue().getTerm(script, sort, termVar);
			acc = Util.and(script, acc, newTerm);
		}
		return acc;
	}

	private Term getTermVar(String varName) {
		IBoogieVar var = mMapVarToBoogieVar.get(varName);
		if (var instanceof BoogieVar) {
			return ((BoogieVar) var).getTermVariable();
		} else if (var instanceof BoogieConst) {
			return ((BoogieConst) var).getDefaultConstant();
		}
		return null;
	}

	// TODO test
	@Override
	public OctagonDomainState patch(OctagonDomainState dominator) {
		OctagonDomainState patchedState = shallowCopy();
		BidirectionalMap<Integer, Integer> mapSourceVarToTargetVar = new BidirectionalMap<>();
		SortedMap<Integer, String> mapDominatorIndicesOfNewNumericVars = new TreeMap<>();

		for (Map.Entry<String, IBoogieVar> entry : dominator.mMapVarToBoogieVar.entrySet()) {
			String var = entry.getKey();
			IBoogieVar newBoogieVar = entry.getValue();
			unrefMapVarToBoogieVar(patchedState);
			IBoogieVar oldBoogieVar = patchedState.mMapVarToBoogieVar.put(var, newBoogieVar);
			assert oldBoogieVar == null || mMapVarToBoogieVar.get(var) == newBoogieVar
					: "Patch caused name-collision: " + var;
			IType type = newBoogieVar.getIType();
			if (TypeUtil.isNumeric(type)) {
				int sourceVar = dominator.mMapNumericVarToIndex.get(var);
				if (oldBoogieVar == null) {
					mapDominatorIndicesOfNewNumericVars.put(sourceVar, var);
					if (TypeUtil.isNumericNonInt(type)) {
						unrefNumericNonIntVars(patchedState);
						patchedState.mNumericNonIntVars.add(var);
					}
				} else {
					int targetVar = patchedState.mMapNumericVarToIndex.get(var);
					mapSourceVarToTargetVar.put(sourceVar, targetVar);
				}
			} else if (TypeUtil.isBoolean(type)){
				unrefBooleanAbstraction(patchedState);
				patchedState.mBooleanAbstraction.put(var, dominator.mBooleanAbstraction.get(var));
			}
			// else: variable has unsupported type and is assumed to be \top
		}
		for (String var : mapDominatorIndicesOfNewNumericVars.values()) {
			unrefMapNumericVarToIndex(patchedState);
			patchedState.mMapNumericVarToIndex.put(var, patchedState.mMapNumericVarToIndex.size());
		}
		patchedState.mNumericAbstraction = patchedState.mNumericAbstraction
				.appendSelection(dominator.mNumericAbstraction, mapDominatorIndicesOfNewNumericVars.keySet());
		unrefNumericAbstraction(patchedState);
		patchedState.mNumericAbstraction.copySelection(dominator.mNumericAbstraction, mapSourceVarToTargetVar);
		return patchedState;
	}

	public OctagonDomainState copyValuesOnScopeChange(OctagonDomainState source,
			Map<String, String> mapSourceToTarget) {
		BidirectionalMap<Integer, Integer> mapNumericSourceToTarget = new BidirectionalMap<>();
		Map<String, String> mapBooleanSourceToTarget = new HashMap<>();

		// shared (=global) numeric variables (copy to keep relations between globals and in/out-parameters)
		for (String var : sharedVars(source)) {
			Integer targetIndex = mMapNumericVarToIndex.get(var);
			if (targetIndex != null) {
				Integer sourceIndex = source.mMapNumericVarToIndex.get(var);
				assert sourceIndex != null : "shared variables are not really shared";
				mapNumericSourceToTarget.put(sourceIndex, targetIndex);
			}
			// do not copy shared (=global) booleans (again). Already done by patch(...).
		}

		// in/out-parameters (from one scope) to locals (from another scope)
		for (Map.Entry<String, String> entry : mapSourceToTarget.entrySet()) {
			String sourceVar = entry.getKey();
			String targetVar = entry.getValue();
			Integer targetIndex = mMapNumericVarToIndex.get(targetVar);
			if (targetIndex != null) {
				Integer sourceIndex = source.mMapNumericVarToIndex.get(sourceVar);
				assert sourceIndex != null : "assigned non-numeric var to numeric var";
				mapNumericSourceToTarget.put(sourceIndex, targetIndex);
			} else if (mBooleanAbstraction.containsKey(targetVar)) {
				assert source.mBooleanAbstraction.containsKey(sourceVar) : "assigned non-boolean var to boolean var";
				mapBooleanSourceToTarget.put(sourceVar, targetVar);
			}
		}

		// create new state
		OctagonDomainState newState = shallowCopy();
		if (!mapNumericSourceToTarget.isEmpty()) {
			unrefNumericAbstraction(newState);
			newState.mNumericAbstraction.copySelection(source.mNumericAbstraction, mapNumericSourceToTarget);
		}
		if (!mapBooleanSourceToTarget.isEmpty()) {
			unrefBooleanAbstraction(newState);
			for (Map.Entry<String, String> entry : mapBooleanSourceToTarget.entrySet()) {
				String sourceVar = entry.getKey();
				BoolValue sourceValue = source.mBooleanAbstraction.get(sourceVar);
				String targetVar = entry.getValue();
				newState.mBooleanAbstraction.put(targetVar, sourceValue);
			}
		}
		return newState;
	}

	//	/**
//	 * Finds the shared global variables and constants between {@code this} and an {@code other} abstract domain state.
//	 * Found global variables and constants are added to existing collections.
//	 * <p>
//	 * Shared variables/constants are the exact same variables/constants.
//	 * Different variables/constants with equal names or even equal types are not shared.
//	 *
//	 * @param other abstract domain state
//	 * @param sharedGlobals collection where the shared global variables are added or {@code null}
//	 * @param sharedConstants collection where the shared constants are added or {@code null}
//	 */
//	public void sharedNumericGlobals(OctagonDomainState other,
//			Collection<String> sharedGlobals, Collection<String> sharedConstants) {
//		for (Map.Entry<String, IBoogieVar> var : sharedVars(other)) {
//			IBoogieVar ibv = var.getValue();
//			if (isNumeric(ibv.getIType())) {
//				if (sharedConstants != null && ibv instanceof BoogieConst) {
//					sharedConstants.add(var.getKey());
//				} else if (sharedGlobals != null && ibv instanceof BoogieVar && ((BoogieVar) ibv).isGlobal()) {
//					sharedGlobals.add(var.getKey());
//				}
//			}
//		}
//	}

	public Set<String> sharedVars(OctagonDomainState other) {
		Set<String> sharedVars = new HashSet<>();
		Set<Map.Entry<String, IBoogieVar>> otherEntrySet = other.mMapVarToBoogieVar.entrySet();
		for (Map.Entry<String, IBoogieVar> entry : mMapVarToBoogieVar.entrySet()) {
			if (otherEntrySet.contains(entry)) {
				sharedVars.add(entry.getKey());
			}
		}
		return sharedVars;
	}

	// TODO buffer vars and havoc all at once => Less closure computations and copies, high speedup.
	// TODO Only calculate closure if necessary. Some vars may have no constraints to other vars => no closure 
	protected void havocVar(String var) {
		Integer v = mMapNumericVarToIndex.get(var);
		if (v != null) {
			mNumericAbstraction = cachedNormalizedNumericAbstraction().copy(); // reduces information loss
			// reset column (also resets row by coherence)
			for (int i = 0; i < mNumericAbstraction.getSize(); ++i) {
				for (int j = 2*v; j < 2*v + 2; ++j) {
					mNumericAbstraction.set(i, j, OctValue.INFINITY);
				}
			}
		} else if (mBooleanAbstraction.containsKey(var)) {
			mBooleanAbstraction.put(var, BoolValue.TOP);
		}
		// else: variables of unsupported types are assumed to be \top all the time
		assert mMapVarToBoogieVar.containsKey(var) : "introduced new variable " + var;
	}

	protected void assignNumericVarConstant(String targetVar, OctValue constant) {
		mNumericAbstraction.assignVarConstant(numVarIndex(targetVar), constant);
	}

	protected void assignNumericVarInterval(String targetVar, OctValue min, OctValue max) {
		mNumericAbstraction.assignVarInterval(numVarIndex(targetVar), min, max);
	}

	// v := v + c;
	protected void incrementNumericVar(String targetVar, OctValue addConstant) {
		mNumericAbstraction.incrementVar(numVarIndex(targetVar), addConstant);
	}

	private int numVarIndex(String var) {
		Integer index = mMapNumericVarToIndex.get(var);
		assert index != null : "Not a numeric variable: " + var;
		return index;
	}
	
	protected void copyVars(Map<String, String> mapSourceVarToTargetVar) {
		for (Map.Entry<String, String> entry : mapSourceVarToTargetVar.entrySet()) {
			String sourceVar = entry.getKey();
			String targetVar = entry.getValue();
			copyVar(targetVar, sourceVar, false);
		}
	}

	// targetVar := (+/-)sourceVar
	protected void copyVar(String targetVar, String sourceVar, boolean negate) {
		Integer targetIndex = mMapNumericVarToIndex.get(targetVar);
		if (targetIndex != null) {
			Integer sourceIndex = mMapNumericVarToIndex.get(sourceVar);
			assert sourceIndex != null : "Incompatible types";
			mNumericAbstraction.copyVar(targetIndex, sourceIndex, negate);
		} else if (mBooleanAbstraction.containsKey(targetIndex)) {
			BoolValue value = mBooleanAbstraction.get(sourceVar);
			assert value != null : "Incompatible types";
			if (negate) {
				value = value.not();
			}
			mBooleanAbstraction.put(targetVar, value);
		}
		// else: variables of unsupported types are assumed to be \top all the time
		assert mMapVarToBoogieVar.containsKey(targetVar) && mMapVarToBoogieVar.containsKey(sourceVar)
			: "unknown variable in assignment: " + targetVar + " := " + sourceVar;
	}
	

	protected void assignBooleanVar(String var, BoolValue value) {
		assert mBooleanAbstraction.containsKey(var) : "introduced new boolean variable " + var;
		mBooleanAbstraction.put(var, value);
	}

	@Override
	public String toLogString() {
		StringBuilder log = new StringBuilder();
		log.append("\n");
		log.append("#" + mId + "\n"); // TODO remove
		log.append(mNumericAbstraction);
		log.append("numeric vars: ");
		log.append(mMapNumericVarToIndex);
		log.append("\n");
		log.append("numeric non-int vars: ");
		log.append(mNumericNonIntVars);
		log.append("\n");
//		log.append(mBooleanAbstraction);
		for (Map.Entry<String, BoolValue> entry : mBooleanAbstraction.entrySet()) {
			log.append(entry.getKey());
			log.append(" = ");
			log.append(entry.getValue());
			log.append("\n");
		}
		return log.toString();
	}

	@Override
	public String toString() {
		return toLogString();
	}
}
