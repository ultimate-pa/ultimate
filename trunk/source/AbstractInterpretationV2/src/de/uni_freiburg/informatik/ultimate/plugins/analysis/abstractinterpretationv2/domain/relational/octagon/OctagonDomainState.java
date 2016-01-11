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

import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.BidirectionalMap;

public class OctagonDomainState implements IAbstractState<OctagonDomainState, CodeBlock, IBoogieVar> {
	
	private static int sId;
	
	/** A human-readable hash code, unique for each object. */
	private final int mId;
	
	private boolean mIsFixpoint;
	
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
	
	private Set<OctagonDomainState> allStates = new HashSet<>(); // TODO remove
	
	private OctagonDomainState() {
		mId = sId++;
		allStates.add(this);
	}
	
	private OctagonDomainState shallowCopy() {
		OctagonDomainState s = new OctagonDomainState();
		s.mIsFixpoint = mIsFixpoint;
		s.mMapVarToBoogieVar = mMapVarToBoogieVar;
		s.mMapNumericVarToIndex = mMapNumericVarToIndex;
		s.mNumericNonIntVars = mNumericNonIntVars;
		s.mNumericAbstraction = mNumericAbstraction;
		s.mBooleanAbstraction = mBooleanAbstraction;
		return s;
	}
	
	public OctagonDomainState deepCopy() {
		OctagonDomainState s = new OctagonDomainState();
		s.mIsFixpoint = mIsFixpoint;
		s.mMapVarToBoogieVar = new HashMap<>(mMapVarToBoogieVar);
		s.mMapNumericVarToIndex = new HashMap<>(mMapNumericVarToIndex);
		s.mNumericNonIntVars = new HashSet<>(mNumericNonIntVars);
		s.mNumericAbstraction = mNumericAbstraction.copy();
		s.mBooleanAbstraction = new HashMap<>(mBooleanAbstraction);
		return s;
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
		OctagonDomainState newState = shallowCopy();
		newState.mMapVarToBoogieVar = new HashMap<>(mMapVarToBoogieVar);
		newState.mMapVarToBoogieVar.putAll(variables);
		for (Map.Entry<String, IBoogieVar> entry : variables.entrySet()) {
			String name = entry.getKey();
			IBoogieVar var = entry.getValue();
			IType type = var.getIType();
			if (isNumeric(type)) {
				unrefMapNumericVarToIndex(newState);
				newState.mMapNumericVarToIndex.put(name, newState.mMapNumericVarToIndex.size());
				if (isNumericNonInteger(type)) {
					unrefNumericNonIntVars(newState);
					newState.mNumericNonIntVars.add(name);
				}
			} else if (isBoolean(type)) {
				unrefBooleanAbstraction(newState);
				newState.mBooleanAbstraction.put(name, BoolValue.TOP);
			}
			// else: variable has unsupported type and is assumed to be \top at all times
		}
		newState.mNumericAbstraction = mNumericAbstraction
				.addVariables(newState.mMapNumericVarToIndex.size() - mMapNumericVarToIndex.size());
		return newState;
	}

	public static boolean isNumeric(IType type) {
		if (type instanceof PrimitiveType) {
			int typeCode = ((PrimitiveType) type).getTypeCode();
			return  typeCode == PrimitiveType.INT || typeCode == PrimitiveType.REAL;
		}
		return false;
	}
	
	public static boolean isNumericNonInteger(IType type) {
		if (type instanceof PrimitiveType) {
			int typeCode = ((PrimitiveType) type).getTypeCode();
			return typeCode == PrimitiveType.REAL;
		}
		return false;
	}
	
	public static boolean isBoolean(IType type) {
		if (type instanceof PrimitiveType) {
			int typeCode = ((PrimitiveType) type).getTypeCode();
			return typeCode == PrimitiveType.BOOL;
		}
		return false;
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
		}
		newState.mNumericAbstraction = normalizedNumericAbstraction().removeVariables(indexRemovedNumericVars);
		return newState;
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
	
	private void unrefBooleanAbstraction(OctagonDomainState state) {
		if (state.mBooleanAbstraction == mBooleanAbstraction) {
			state.mBooleanAbstraction = new HashMap<>(mBooleanAbstraction);
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
		return normalizedNumericAbstraction().hasNegativeSelfLoop();
	}
	
	private boolean isBooleanAbstractionBottom() {
		for (BoolValue b : mBooleanAbstraction.values()) {
			if (b != BoolValue.BOT) {
				return false;
			}
		}
		return true;
	}

	private OctMatrix normalizedNumericAbstraction() {
		if (isNumericAbstractionIntegral()) {
			return mNumericAbstraction.tightClosure();
		} else {
			return mNumericAbstraction.strongClosure();
		}
	}
	
	private boolean isNumericAbstractionIntegral() {
		return mNumericNonIntVars.isEmpty();
	}
	
	@Override
	public boolean isFixpoint() {
		return mIsFixpoint;
	}

	@Override
	public OctagonDomainState setFixpoint(boolean value) {
		if (value == mIsFixpoint) {
			return this;
		}	
		OctagonDomainState newState = shallowCopy();
		newState.mIsFixpoint = value;
		return newState;
	}

	@Override
	public boolean isEqualTo(OctagonDomainState other) {
		if (other == null) {
			return false;
		} else if (other == this) {
			return true;
		} else {
			return mMapVarToBoogieVar.equals(other.mMapVarToBoogieVar)
					&& mBooleanAbstraction.equals(other.mBooleanAbstraction)
					&& numericAbstractionIsEqualTo(other);
		}
	}
	
	@Override
	public int hashCode() {
		return mId;
	}
	
	private boolean numericAbstractionIsEqualTo(OctagonDomainState other) {
		// TODO transform the following ifs into assertions
		if (!mMapNumericVarToIndex.keySet().equals(other.mMapNumericVarToIndex.keySet())) {
			return false;
		} else if (!mMapNumericVarToIndex.equals(other.mMapNumericVarToIndex)) {
			throw new IllegalStateException("Matrices have same variables but in different order.");
		}
		OctMatrix m = normalizedNumericAbstraction();
		OctMatrix n = other.normalizedNumericAbstraction();
		return (m.hasNegativeSelfLoop() && n.hasNegativeSelfLoop()) || m.isEqualTo(n);
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
		unrefBooleanAbstraction(result);
		for (Map.Entry<String, BoolValue> entry : mBooleanAbstraction.entrySet()) {
			String name = entry.getKey();
			BoolValue value = booleanOperation.apply(entry.getValue(),other.mBooleanAbstraction.get(name));
			result.mBooleanAbstraction.put(name, value);
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
		Map<String, IBoogieVar> mapTypeChangedVarsToNewType = varsWithTypeCategoryCollisions(dominator);
		OctagonDomainState s = this.removeVariables(mapTypeChangedVarsToNewType);
		
		BidirectionalMap<Integer, Integer> mapSourceVarToTargetVar = new BidirectionalMap<>();
		SortedMap<Integer, String> mapOldIndicesOfNewNumericVars = new TreeMap<>();

		for (Map.Entry<String, IBoogieVar> entry : dominator.mMapVarToBoogieVar.entrySet()) {
			String var = entry.getKey();
			IBoogieVar newBoogieVar = entry.getValue();
			s.mMapVarToBoogieVar.put(var, newBoogieVar);
			IType newType = newBoogieVar.getIType();
			if (isNumeric(newType)) {
				int sourceVar = dominator.mMapNumericVarToIndex.get(var);
				Integer targetVar = s.mMapNumericVarToIndex.get(var);
				if (targetVar == null) {
					mapOldIndicesOfNewNumericVars.put(sourceVar, var);
				} else {
					mapSourceVarToTargetVar.put(sourceVar, targetVar);
				}
				if (isNumericNonInteger(newType)) {
					s.mNumericNonIntVars.add(var);
				} else {
					s.mNumericNonIntVars.remove(var);
				}
			} else if (isBoolean(newType)){
				s.mBooleanAbstraction.put(var, dominator.mBooleanAbstraction.get(var));
			}
			// else: variable has unsupported type and is assumed to be \top
		}
		for (String var : mapOldIndicesOfNewNumericVars.values()) {
			s.mMapNumericVarToIndex.put(var, s.mMapNumericVarToIndex.size());
		}
		s.mNumericAbstraction
				.overwriteSelection(dominator.mNumericAbstraction, mapSourceVarToTargetVar);
		s.mNumericAbstraction = s.mNumericAbstraction
				.appendSelection(dominator.mNumericAbstraction, mapOldIndicesOfNewNumericVars.keySet());
		return s;
	}

	/**
	 * Searches variables with the same name in {@code this} and {@code dominator} but different type categories.
	 * The return value can be used in {@link #removeVariables(Map)}.
	 * 
	 * @param dominator other state
	 * @return map from colliding variable (names) to their {@linkplain IBoogieVar} from {@code this} state
	 * 
	 * @see #typeCategoryEquals(IType, IType)
	 */
	private Map<String, IBoogieVar> varsWithTypeCategoryCollisions(OctagonDomainState dominator) {
		HashMap<String, IBoogieVar> typeChangedVars = new HashMap<>();
		for (Map.Entry<String, IBoogieVar> entry : dominator.mMapVarToBoogieVar.entrySet()) {
			String var = entry.getKey();
			IBoogieVar newBoogieVar = entry.getValue();
			IBoogieVar oldBoogieVar = mMapVarToBoogieVar.get(var);
			if (oldBoogieVar != null && !typeCategoryEquals(oldBoogieVar.getIType(), oldBoogieVar.getIType())) {
				typeChangedVars.put(var, newBoogieVar);
			}
		}
		return typeChangedVars;
	}
	
	protected void havocVar(String var) {
		Integer v = mMapNumericVarToIndex.get(var);
		if (v != null) {
			mNumericAbstraction = normalizedNumericAbstraction(); // reduces information loss
			// reset column (also resets row by coherence)
			for (int i = 0; i < mNumericAbstraction.getSize(); ++i) {
				for (int j = 2*v; j < 2*v + 2; ++j) {
					mNumericAbstraction.set(i, j, OctValue.INFINITY);
				}
			}
		} else if (mBooleanAbstraction.containsKey(var)) {
			assert mBooleanAbstraction.containsKey(var) : "introduced new variable " + var;
			mBooleanAbstraction.put(var, BoolValue.TOP);
		}
		// else: variables of unsupported types are assumed to be \top all the time
		assert mMapVarToBoogieVar.containsKey(var) : "introduced new variable " + var;
	}

	protected void assignNumericVarConstant(String var, OctValue value) {
		assignNumericVarInterval(var, value, value);
	}

	protected void assignNumericVarInterval(String var, OctValue min, OctValue max) {
		havocVar(var);
		int v2 = mMapNumericVarToIndex.get(var) * 2;
		mNumericAbstraction.set(v2, v2 + 1, min.add(min).negate());
		mNumericAbstraction.set(v2 + 1, v2, max.add(max));
	}

	// v1 := v2 + c;
	protected void assignNumericVarRelational(String var, String otherVar, OctValue addConstant) {
		OctValue addConstantNegated = addConstant.negate();
		Integer v2 = mMapNumericVarToIndex.get(var) * 2;
		if (var.equals(otherVar)) {
			// update column (row is updated by coherence)
			for (int i = 0; i < mNumericAbstraction.getSize(); ++i) {
				int beta = 0;
				if (i == v2) {
					beta = -1;
				} else if (i == v2 + 1) {
					beta = 1;
				}
				for (int j = v2; j < v2 + 2; ++j) {
					int alpha = (j == v2) ? 1 : -1;
					int factor = alpha + beta;
					if (factor == 1) {
						mNumericAbstraction.set(i, j, mNumericAbstraction.get(i, j).add(addConstant));
					} else if (factor == -1) {
						mNumericAbstraction.set(i, j, mNumericAbstraction.get(i, j).add(addConstantNegated));
					}
				}
			}
		} else {
			Integer ov2 = mMapNumericVarToIndex.get(var) * 2;
			havocVar(var);
			mNumericAbstraction.set(ov2, v2, addConstant); // also entry (v2 + 1, ov2 + 1) by coherence
			mNumericAbstraction.set(v2, ov2, addConstantNegated); // also entry (ov2 + 1, v2 + 1) by coherence
		}
	}
	
	protected void assignBooleanVar(String var, BoolValue value) {
		assert mBooleanAbstraction.containsKey(var) : "introduced new boolean variable " + var;
		mBooleanAbstraction.put(var, value);
	}
	
	/**
	 * Checks if two Boogie types are of the same type category.
	 * There are three type categories:
	 * numeric (int, real),
	 * bool (bool),
	 * and unsupported types (bit-vectors, arrays, ...).
	 *
	 * @param a first type
	 * @param b second type
	 * @return a and b are of the same abstract type
	 */
	private boolean typeCategoryEquals(IType a, IType b) {
		return (isBoolean(a) == isBoolean(b)) && (isNumeric(a) == isNumeric(b));
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
