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
	private final int mId;
	
	private boolean mIsFixpoint;
	
	private Map<String, IBoogieVar> mMapVariableToType;
	private Map<String, Integer> mMapNumericVariableToIndex;
	private Set<String> mNumericNonIntegerVariables;
	private OctMatrix mNumericAbstraction;
	private Map<String, BooleanValue> mBooleanAbstraction;

	public static OctagonDomainState createFreshState() {
		OctagonDomainState s = new OctagonDomainState();
		s.mMapVariableToType = new HashMap<>();
		s.mMapNumericVariableToIndex = new HashMap<>();
		s.mNumericNonIntegerVariables = new HashSet<>();
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
		s.mMapVariableToType = mMapVariableToType;
		s.mMapNumericVariableToIndex = mMapNumericVariableToIndex;
		s.mNumericNonIntegerVariables = mNumericNonIntegerVariables;
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
		newState.mMapVariableToType = new HashMap<>(mMapVariableToType);
		newState.mMapVariableToType.putAll(variables);
		for (Map.Entry<String, IBoogieVar> entry : variables.entrySet()) {
			String name = entry.getKey();
			IBoogieVar var = entry.getValue();
			IType type = var.getIType();
			if (isNumeric(type)) {
				unrefMapNumericVariableToIndex(newState);
				newState.mMapNumericVariableToIndex.put(name, newState.mMapNumericVariableToIndex.size());
				if (!isInteger(type)) {
					unrefNumericNonIntegerVariables(newState);
					newState.mNumericNonIntegerVariables.add(name);
				}
			} else if (type instanceof BooleanValue) {
				unrefBooleanAbstraction(newState);
				newState.mBooleanAbstraction.put(name, new BooleanValue());
			} else {
				throw new UnsupportedOperationException("Variables of type " + type + " are not supported.");
			}
		}
		newState.mNumericAbstraction =
				mNumericAbstraction.addVariables(mMapNumericVariableToIndex.size() - mNumericAbstraction.variables());
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
		newState.mMapVariableToType = new HashMap<>(mMapVariableToType);
		Set<Integer> indexRemovedNumericVars = new HashSet<>();
		for (String name : variables.keySet()) {
			newState.mMapVariableToType.remove(name);
			if (newState.mMapNumericVariableToIndex.containsKey(name)) {
				unrefMapNumericVariableToIndex(newState);
				int i = newState.mMapNumericVariableToIndex.remove(name);
				indexRemovedNumericVars.add(i);
				if (mNumericNonIntegerVariables.contains(name)) {
					unrefNumericNonIntegerVariables(newState);
					newState.mNumericNonIntegerVariables.remove(name);
				}
			} else {
				unrefBooleanAbstraction(newState);
				newState.mBooleanAbstraction.remove(name);
			}
		}
		newState.mNumericAbstraction = mNumericAbstraction.removeVariables(indexRemovedNumericVars);
		return newState;
	}

	private void unrefMapNumericVariableToIndex(OctagonDomainState state) {
		if (state.mMapNumericVariableToIndex == mMapNumericVariableToIndex) {
			state.mMapNumericVariableToIndex = new HashMap<>(mMapNumericVariableToIndex);
		}
	}

	private void unrefNumericNonIntegerVariables(OctagonDomainState state) {
		if (state.mNumericNonIntegerVariables == mNumericNonIntegerVariables) {
			state.mNumericNonIntegerVariables = new HashSet<>(mNumericNonIntegerVariables);
		}		
	}
	
	private void unrefBooleanAbstraction(OctagonDomainState state) {
		if (state.mBooleanAbstraction == mBooleanAbstraction) {
			state.mBooleanAbstraction = new HashMap<>(mBooleanAbstraction);
		}
	}
	
	@Override
	public IBoogieVar getVariableType(String name) {
		return mMapVariableToType.get(name);
	}

	@Override
	public boolean containsVariable(String name) {
		return mMapVariableToType.containsKey(name);
	}

	@Override
	public boolean isEmpty() {
		return mMapVariableToType.isEmpty();
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
		return mNumericNonIntegerVariables.isEmpty();
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
		return mMapVariableToType.equals(other.mMapVariableToType)
				&& mBooleanAbstraction.equals(other.mBooleanAbstraction) && numericAbstractionIsEqualTo(other);
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
	
	public OctagonDomainState widen(OctagonDomainState other) {
		return operation(other, BooleanValue::merge, OctMatrix::widen);
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
		return this; // OctagonDomainStates are immutable
	}

	@Override
	public String toLogString() {
		// TODO Auto-generated method stub
		return "log string not implemented";
	}

}
