package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class OctagonDomainState
		implements IAbstractState<OctagonDomainState, CodeBlock, IBoogieVar> {
	
	private static int sId;
	
	/** A human-readable hash code, unique for each object. */
	private final int mId;
	
	private boolean mIsFixpoint;
	
	private Map<String, IBoogieVar> mMapVarToBoogieVar;
	private Map<String, Integer> mMapNumericVarToIndex;
	private Set<String> mNumericNonIntVars;
	private OctMatrix mNumericAbstraction;
	private Map<String, BooleanValue> mBooleanAbstraction;

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
	
	private OctagonDomainState shallowCopy() {
		OctagonDomainState s = new OctagonDomainState();
		s.mIsFixpoint = mIsFixpoint;
		s.mMapVarToBoogieVar = mMapVarToBoogieVar;
		s.mMapNumericVarToIndex = mMapNumericVarToIndex;
		s.mNumericNonIntVars = mNumericNonIntVars;
		s.mBooleanAbstraction = mBooleanAbstraction;
		return s;
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
				if (!isInteger(type)) {
					unrefNumericNonIntVars(newState);
					newState.mNumericNonIntVars.add(name);
				}
			} else if (type instanceof BooleanValue) {
				unrefBooleanAbstraction(newState);
				newState.mBooleanAbstraction.put(name, new BooleanValue());
			} else {
				throw new UnsupportedOperationException("Variables of type " + type + " are not supported.");
			}
		}
		newState.mNumericAbstraction =
				mNumericAbstraction.addVariables(mMapNumericVarToIndex.size() - mNumericAbstraction.variables());
		return newState;
	}

	private boolean isNumeric(IType type) {
		if (type instanceof PrimitiveType) {
			int typeCode = ((PrimitiveType) type).getTypeCode();
			return  typeCode == PrimitiveType.INT || typeCode == PrimitiveType.REAL;
		} else if (type instanceof ArrayType) {
			return isNumeric(((ArrayType) type).getValueType());
		} else {
			return false;
		}
	}

	private boolean isInteger(IType type) {
		if (type instanceof PrimitiveType) {
			int typeCode = ((PrimitiveType) type).getTypeCode();
			return  typeCode == PrimitiveType.INT;
		} else if (type instanceof ArrayType) {
			return isNumeric(((ArrayType) type).getValueType());
		} else {
			return false;
		}
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
			} else {
				unrefBooleanAbstraction(newState);
				newState.mBooleanAbstraction.remove(name);
			}
		}
		newState.mNumericAbstraction = mNumericAbstraction.removeVariables(indexRemovedNumericVars);
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
		return isBooleanAbstractionBottom() && isNumericAbstractionBottom();
	}
	
	private boolean isNumericAbstractionBottom() {
		return normalizedNumericAbstraction().hasNegativeSelfLoop();
	}
	
	private boolean isBooleanAbstractionBottom() {
		for (BooleanValue b : mBooleanAbstraction.values()) {
			if (b.getValue() != BooleanValue.Value.BOTTOM) {
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
		return mMapVarToBoogieVar.equals(other.mMapVarToBoogieVar)
				&& mBooleanAbstraction.equals(other.mBooleanAbstraction) && numericAbstractionIsEqualTo(other);
	}
	
	@Override
	public int hashCode() {
		return mId;
	}
	
	private boolean numericAbstractionIsEqualTo(OctagonDomainState other) {
		OctMatrix m = normalizedNumericAbstraction();
		OctMatrix n = other.normalizedNumericAbstraction();
		return (m.hasNegativeSelfLoop() && n.hasNegativeSelfLoop()) || m.isEqualTo(n);
	}

	public OctagonDomainState meet(OctagonDomainState other) {
		return operation(other, BooleanValue::intersect, OctMatrix::min);
	}
	
	public OctagonDomainState join(OctagonDomainState other) {
		return operation(other, BooleanValue::merge, OctMatrix::max);
	}
	
	public OctagonDomainState widen(OctagonDomainState other, BiFunction<OctMatrix, OctMatrix, OctMatrix> widenOp) {
		return operation(other, BooleanValue::merge, widenOp);
	}

	private OctagonDomainState operation(OctagonDomainState other,
			BiFunction<BooleanValue, BooleanValue, BooleanValue> booleanOperation,
			BiFunction<OctMatrix, OctMatrix, OctMatrix> numericOperation) {		
		OctagonDomainState result = shallowCopy();
		unrefBooleanAbstraction(result);
		for (Map.Entry<String, BooleanValue> entry : mBooleanAbstraction.entrySet()) {
			String name = entry.getKey();
			BooleanValue value = booleanOperation.apply(entry.getValue(),other.mBooleanAbstraction.get(name));
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
		Term b = getTermNumericBooleanAbstraction(script, bpl2smt);
		return Util.and(script, n, b);
	}
	
	private Term getTermNumericAbstraction(Script script, Boogie2SMT bpl2smt) {		
		Term acc = script.term("true");
		// TODO implement
		return acc;
	}
	
	private Term getTermNumericBooleanAbstraction(Script script, Boogie2SMT bpl2smt) {
		Term acc = script.term("true");
		// TODO implement
		return acc;
	}
	
	@Override
	public OctagonDomainState copy() {
		throw new UnsupportedOperationException();
	}

	@Override
	public String toLogString() {
		// TODO Auto-generated method stub
		return "log string not implemented";
	}

}
