package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.VariableArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.VariableBooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.VariableTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.VariableIntegerTerm;

public class VariableSet {
	private final HashMap<TermVariable, Variable> inVars = new HashMap<>();
	private final HashMap<TermVariable, Variable> outVars = new HashMap<>();
	private final HashMap<TermVariable, Variable> auxVars = new HashMap<>();
	private final HashMap<TermVariable, Variable> allVars = new HashMap<>();
	private final HashSet<Variable> allExecutionVars = new HashSet<>();

	public Variable getVariable(final TermVariable termVar) {
		return allVars.get(termVar);
	}

	public HashSet<Variable> getVariables() {
		return allExecutionVars;
	}

	public HashMap<TermVariable, Variable> getOutVars() {
		return outVars;
	}

	public HashMap<TermVariable, Variable> getInVars() {
		return inVars;
	}

	public void addVariable(final boolean isInVar, final boolean isOutVar, final boolean isAuxVar,
			final boolean isAssignable, final IProgramVar progVariable, final TermVariable termVariable) {
		final Sort sort = termVariable.getDeclaredSort();
		final VariableTerm variableTerm = new VariableTerm(isInVar, isOutVar, isAuxVar, isAssignable, progVariable,
				termVariable);
		Variable variable = null;
		switch (Util.getType(sort)) {
		case Array:
			final ReturnType valueType = Util.getType(sort.getArguments()[1]);
			final ReturnType keyType = Util.getType(sort.getArguments()[0]);
			variable = new VariableArrayTerm(keyType, valueType, variableTerm);
			break;
		case BitVector:
			// TODO
			break;
		case Boolean:
			variable = new VariableBooleanTerm(variableTerm);
			break;
		case Int:
			variable = new VariableIntegerTerm(variableTerm);
			break;
		}

		if (variable == null) {
			return;
		}

		allVars.put(termVariable, variable);
		allExecutionVars.add(variable);

		if (isInVar) {
			inVars.put(termVariable, variable);
		}
		if (isOutVar) {
			outVars.put(termVariable, variable);
		}
		if (isAuxVar) {
			auxVars.put(termVariable, variable);
		}
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof VariableSet)) {
			return false;
		}
		final VariableSet bCast = (VariableSet) b;
		return allExecutionVars.equals(bCast.allExecutionVars);
	}

	@Override
	public int hashCode() {
		return super.hashCode();
	}
}
