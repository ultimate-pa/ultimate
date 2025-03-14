package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class ProgramState {
	private final HashMap<IProgramVar, Boolean> boolVars = new HashMap<>();
	private final HashMap<IProgramVar, Integer> intVars = new HashMap<>();
	private final HashMap<IProgramVar, SMTArray> arrayVars = new HashMap<>();
	private final HashMap<IProgramVar, BitVector> bvVars = new HashMap<>();

	public ProgramState(final ArrayList<Variable> allVariables) {
		for (final Variable variable : allVariables) {
			switch (variable.getTerm().returnType) {
			case Array:
				arrayVars.put(variable.getVariableTerm().programVar, null);
				break;
			case BitVector:
				bvVars.put(variable.getVariableTerm().programVar, null);
				break;
			case Boolean:
				boolVars.put(variable.getVariableTerm().programVar, null);
				break;
			case Int:
				intVars.put(variable.getVariableTerm().programVar, null);
				break;
			}
		}
	}

	public void setValue(final IProgramVar variable, final boolean value) {
		boolVars.put(variable, value);
	}

	public void setValue(final IProgramVar variable, final int value) {
		intVars.put(variable, value);
	}

	public void setValue(final IProgramVar variable, final SMTArray value) {
		arrayVars.put(variable, value);
	}

	public void setValue(final IProgramVar variable, final BitVector value) {
		bvVars.put(variable, value);
	}

	public Boolean getBoolOf(final IProgramVar variable) {
		return boolVars.getOrDefault(variable, null);
	}

	public Integer getIntOf(final IProgramVar variable) {
		return intVars.getOrDefault(variable, null);
	}

	public SMTArray getArrayOf(final IProgramVar variable) {
		return arrayVars.getOrDefault(variable, null);
	}

	public BitVector getBitVectorOf(final IProgramVar variable) {
		return bvVars.getOrDefault(variable, null);
	}
}
