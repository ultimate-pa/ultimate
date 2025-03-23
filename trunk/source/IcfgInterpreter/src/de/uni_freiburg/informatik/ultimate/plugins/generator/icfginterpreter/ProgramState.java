package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.VariableArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bitvector.VariableBitVectorTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.VariableBooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.VariableIntegerTerm;

public class ProgramState {
	private final HashMap<IProgramVar, SMTArray> mArrayVars;
	private final HashMap<IProgramVar, Boolean> mBoolVars;
	private final HashMap<IProgramVar, BitVector> mBVVars;
	private final HashMap<IProgramVar, Integer> mIntVars;
	private boolean mFinal;
	private final NonDeterministicChoice mNDC;

	public ProgramState(final ArrayList<Variable> allVariables, final NonDeterministicChoice ndc) {
		mArrayVars = new HashMap<>();
		mBoolVars = new HashMap<>();
		mBVVars = new HashMap<>();
		mIntVars = new HashMap<>();
		for (final Variable variable : allVariables) {
			final IProgramVar programVar = variable.getVariableTerm().programVar;
			if (programVar == null) {
				continue;
			}
			switch (variable.getTerm().returnType) {
			case Array:
				if (mArrayVars.containsKey(programVar)) {
					continue;
				}
				final VariableArrayTerm arrayVariable = (VariableArrayTerm) variable;
				mArrayVars.put(programVar, ndc.newArray(arrayVariable, null));
				break;
			case BitVector:
				if (mBVVars.containsKey(programVar)) {
					continue;
				}
				mBVVars.put(programVar, ndc.havocBitVector((VariableBitVectorTerm) variable, null));
				break;
			case Boolean:
				if (mBoolVars.containsKey(programVar)) {
					continue;
				}
				final VariableBooleanTerm boolVariable = (VariableBooleanTerm) variable;
				mBoolVars.put(programVar, ndc.havocBool(boolVariable, null));
				break;
			case Int:
				if (mIntVars.containsKey(programVar)) {
					continue;
				}
				final VariableIntegerTerm intVariable = (VariableIntegerTerm) variable;
				mIntVars.put(programVar, ndc.havocInt(intVariable, null));
				break;
			}
		}
		mNDC = ndc;
	}

	public ProgramState(final HashMap<IProgramVar, SMTArray> arrayVars, final HashMap<IProgramVar, Boolean> boolVars,
			final HashMap<IProgramVar, BitVector> bvVars, final HashMap<IProgramVar, Integer> intVars,
			final NonDeterministicChoice ndc) {
		mArrayVars = arrayVars;
		mBoolVars = boolVars;
		mBVVars = bvVars;
		mIntVars = intVars;
		mNDC = ndc;
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

	/**
	 * Create a clone of the program state. The clone may be changed, even if the original {@link #isFinalized()} They
	 * use the same {@link NonDeterministicChoice} instance.
	 */
	@Override
	public ProgramState clone() {
		return new ProgramState(Util.copyMap(mArrayVars), Util.copyMap(mBoolVars), Util.copyMap(mBVVars),
				Util.copyMap(mIntVars), mNDC);
	}

	public void setValue(final IProgramVar variable, final boolean value) {
		if (mFinal) {
			assert false;
		}
		mBoolVars.put(variable, value);
	}

	public void setValue(final IProgramVar variable, final int value) {
		if (mFinal) {
			assert false;
		}
		mIntVars.put(variable, value);
	}

	public void setValue(final IProgramVar variable, final SMTArray value) {
		if (mFinal) {
			assert false;
		}
		mArrayVars.put(variable, value);
	}

	public void setValue(final IProgramVar variable, final BitVector value) {
		if (mFinal) {
			assert false;
		}
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

	public void finalizeState() {
		mFinal = true;
	}

	public boolean isFinalized() {
		return mFinal;
	}

	public NonDeterministicChoice getNDC() {
		return mNDC;
	}
}
