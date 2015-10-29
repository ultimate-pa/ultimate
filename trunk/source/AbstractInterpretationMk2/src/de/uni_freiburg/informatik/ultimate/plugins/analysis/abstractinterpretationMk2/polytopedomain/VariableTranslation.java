package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;
import parma_polyhedra_library.Variable;

/**
 * Translates boogie variables into dimensions All polytopes which describe
 * states in a same scope must reference to the same VariableTranslation
 * 
 * @author Jan Hättig
 *
 */
public class VariableTranslation {
	/**
	 * Mapping from the abstract variables to the variables in the polytope
	 */
	private Map<TypedAbstractVariable, Variable> mVars2PPLVars;
	private Map<Variable, TypedAbstractVariable> mPPLVars2Vars;

	/**
	 * To enumerate the variables
	 */
	private long mNextIndex;

	/**
	 * ID for debugging
	 */
	private final int mUID;

	private static int sNextUID = 0;

	/**
	 * Constructor
	 */
	public VariableTranslation() {
		mVars2PPLVars = new HashMap<>();
		mPPLVars2Vars = new HashMap<>();
		mNextIndex = 0;
		mUID = sNextUID++;
	}

	/**
	 * Copy Constructor. Creates a copy of this (with no shared references
	 */
	public VariableTranslation(VariableTranslation vt) {
		mNextIndex = vt.mNextIndex;
		mVars2PPLVars = new HashMap<>(vt.mVars2PPLVars);
		mPPLVars2Vars = new HashMap<>(vt.mPPLVars2Vars);
		mUID = sNextUID++;
	}

	public int size() {
		return mVars2PPLVars.size();
	}

	/**
	 * Adds a variable to the scope. The states dimensions must still be updated
	 * 
	 * @param variable
	 * @return
	 */
	public Variable addVariable(TypedAbstractVariable variable) {
		final Variable x = new Variable(mNextIndex++);
		add(variable, x);
		return x;
	}

	public Variable addShiftedVariable(TypedAbstractVariable variable, long dimension) {
		assert dimension > mNextIndex;
		mNextIndex = dimension + 1;
		final Variable x = new Variable(dimension);

		add(variable, x);
		return x;
	}

	public Set<Entry<TypedAbstractVariable, Variable>> entries() {
		return mVars2PPLVars.entrySet();
	}

	/**
	 * Removes a variable to the scope. The states dimensions must still be
	 * updated
	 * 
	 * @param variable
	 * @return
	 */
	public Variable removeVariable(TypedAbstractVariable variable) {
		final Variable rtr = mVars2PPLVars.remove(variable);
		if (rtr != null) {
			mPPLVars2Vars.remove(rtr);
		}
		return rtr;
	}

	/**
	 * Adds the given prefix to all variables.
	 * 
	 * @param prefix
	 */
	public void addPrefix(String prefix) {
		final Map<TypedAbstractVariable, Variable> newVar2PPLVar = new HashMap<>();
		final Map<Variable, TypedAbstractVariable> newPPLVar2Var = new HashMap<>();
		for (Entry<TypedAbstractVariable, Variable> entry : mVars2PPLVars.entrySet()) {
			final TypedAbstractVariable oldtypedvar = entry.getKey();
			final TypedAbstractVariable newtypedvar = new TypedAbstractVariable(prefix + oldtypedvar.getString(),
					oldtypedvar.getDeclaration(), oldtypedvar.getType());

			newVar2PPLVar.put(newtypedvar, entry.getValue());
			newPPLVar2Var.put(entry.getValue(), newtypedvar);
		}
		mVars2PPLVars = newVar2PPLVar;
		mPPLVars2Vars = newPPLVar2Var;
	}

	@Override
	public String toString() {
		String output = "[VT_" + mUID + " (#var: " + mNextIndex + ") ";
		String comma = "";
		for (Entry<TypedAbstractVariable, Variable> entry : mVars2PPLVars.entrySet()) {
			output += comma + entry.getKey().getString() + " -> " + entry.getValue().toString();
			comma = ", ";
		}
		return output + "]";
	}

	/**
	 * Checks, whether the given table has the same assignment
	 * 
	 * @param variableTranslation
	 * @return
	 */
	public boolean isIdentical(VariableTranslation variableTranslation) {
		for (Entry<TypedAbstractVariable, Variable> entry : mVars2PPLVars.entrySet()) {
			Variable other = variableTranslation.mVars2PPLVars.get(entry.getKey());
			if (other == null || entry.getValue().id() != other.id()) {
				return false;
			}
		}
		for (Entry<TypedAbstractVariable, Variable> entry : variableTranslation.mVars2PPLVars.entrySet()) {
			Variable other = mVars2PPLVars.get(entry.getKey());
			if (other == null || entry.getValue().id() != other.id()) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Adds all missing variables which are missing in one table to the other.
	 * (If it is not already assigned otherwise)
	 * 
	 * @param other
	 * @return returns whether the operation was successful
	 */
	public boolean union(VariableTranslation other) {
		// from this to other
		for (Entry<TypedAbstractVariable, Variable> entry : mVars2PPLVars.entrySet()) {
			Variable otherVar = other.mVars2PPLVars.get(entry.getKey());
			// if not existing
			if (otherVar == null) {
				other.add(entry.getKey(), entry.getValue());
			} else if (entry.getValue().id() != otherVar.id()) {
				return false;
			}
		}

		// other to this
		for (Entry<TypedAbstractVariable, Variable> entry : other.mVars2PPLVars.entrySet()) {
			Variable thisVar = mVars2PPLVars.get(entry.getKey());
			// if not existing
			if (thisVar == null) {
				add(entry.getKey(), entry.getValue());
			} else if (entry.getValue().id() != thisVar.id()) {
				return false;
			}
		}
		return true;
	}

	public TypedAbstractVariable checkVar(Object variable) {
		if (mVars2PPLVars.containsKey(variable)) {
			return (TypedAbstractVariable) variable;
		}
		return null;
	}

	public Variable getPPLVar(Object variable) {
		return mVars2PPLVars.get(variable);
	}

	private void add(TypedAbstractVariable var, Variable pplvar) {
		if (mVars2PPLVars.containsKey(var)) {
			throw new RuntimeException("Variable must not be declared twice");
		}
		mVars2PPLVars.put(var, pplvar);
		mPPLVars2Vars.put(pplvar, var);
	}

	public TypedAbstractVariable getVar(Object arg) {
		return mPPLVars2Vars.get(arg);
	}
}
