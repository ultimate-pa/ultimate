package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.VariableArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.VariableBooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.VariableIntegerTerm;

public class ProgramState {
	private final HashMap<IProgramVar, SMTArray> mArrayVars;
	private final HashMap<IProgramVar, Boolean> mBoolVars;
	private final HashMap<IProgramVar, BitVector> mBVVars;
	private final HashMap<IProgramVar, Integer> mIntVars;

	public ProgramState(final ArrayList<Variable> allVariables, final NonDeterministicChoice ndc) {
		mArrayVars = new HashMap<>();
		mBoolVars = new HashMap<>();
		mBVVars = new HashMap<>();
		mIntVars = new HashMap<>();
		for (final Variable variable : allVariables) {
			switch (variable.getTerm().returnType) {
			case Array:
				final VariableArrayTerm arrayVariable = (VariableArrayTerm) variable;
				mArrayVars.put(variable.getVariableTerm().programVar, ndc.newArray(arrayVariable, null));
				break;
			case BitVector:
				mBVVars.put(variable.getVariableTerm().programVar, ndc.havocBitVector(variable, null));
				break;
			case Boolean:
				final VariableBooleanTerm boolVariable = (VariableBooleanTerm) variable;
				mBoolVars.put(variable.getVariableTerm().programVar, ndc.havocBool(boolVariable, null));
				break;
			case Int:
				final VariableIntegerTerm intVariable = (VariableIntegerTerm) variable;
				mIntVars.put(variable.getVariableTerm().programVar, ndc.havocInt(intVariable, null));
				break;
			}
		}
	}

	public ProgramState(final HashMap<IProgramVar, SMTArray> arrayVars, final HashMap<IProgramVar, Boolean> boolVars,
			final HashMap<IProgramVar, BitVector> bvVars, final HashMap<IProgramVar, Integer> intVars) {
		mArrayVars = arrayVars;
		mBoolVars = boolVars;
		mBVVars = bvVars;
		mIntVars = intVars;
	}

	public HashMap<IProgramVar, Object> getVariableValues() {
		final HashMap<IProgramVar, Object> out = new HashMap<>();
		out.putAll(mArrayVars);
		out.putAll(mBoolVars);
		out.putAll(mBVVars);
		out.putAll(mIntVars);
		return out;
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder();
		for (final Entry<IProgramVar, Object> arrayVariable : getVariableValues().entrySet()) {
			out.append(arrayVariable.getKey().getGloballyUniqueId()).append(" = ");
			out.append(arrayVariable.getValue()).append("\n");
		}
		return out.toString().stripTrailing();
	}

	@Override
	public ProgramState clone() {
		return new ProgramState(Util.copyMap(mArrayVars), Util.copyMap(mBoolVars), Util.copyMap(mBVVars),
				Util.copyMap(mIntVars));
	}

	public void setValue(final IProgramVar variable, final boolean value) {
		mBoolVars.put(variable, value);
	}

	public void setValue(final IProgramVar variable, final int value) {
		mIntVars.put(variable, value);
	}

	public void setValue(final IProgramVar variable, final SMTArray value) {
		mArrayVars.put(variable, value);
	}

	public void setValue(final IProgramVar variable, final BitVector value) {
		mBVVars.put(variable, value);
	}

	public Boolean getBoolOf(final IProgramVar variable) {
		return mBoolVars.getOrDefault(variable, null);
	}

	public Integer getIntOf(final IProgramVar variable) {
		return mIntVars.getOrDefault(variable, null);
	}

	public SMTArray getArrayOf(final IProgramVar variable) {
		return mArrayVars.getOrDefault(variable, null);
	}

	public BitVector getBitVectorOf(final IProgramVar variable) {
		return mBVVars.getOrDefault(variable, null);
	}
}
