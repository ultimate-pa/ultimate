package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain;

import java.util.HashMap;
import java.util.Map.Entry;

import parma_polyhedra_library.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.AbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;

/**
 * Translates boogie variables into dimensions All polytopes which describe
 * states in a same scope must reference to the same VariableTranslation
 * 
 * @author GROSS-JAN
 *
 */
public class VariableTranslation {
	/**
	 * Mapping from the abstract variables to the variables in the polytope
	 */
	private HashMap<TypedAbstractVariable, Variable> mVariables;

	/**
	 * To enumerate the variables
	 */
	private int mNextIndex;

	/**
	 * ID for debugging
	 */
	private final int mUID;

	private static int sNextUID = 0;

	/**
	 * Constructor
	 */
	public VariableTranslation() {
		mVariables = new HashMap<TypedAbstractVariable, Variable>();
		mNextIndex = 0;
		mUID = sNextUID++;
	}

	/**
	 * Copy Constructor. Creates a copy of this (with no shared references
	 */
	public VariableTranslation(VariableTranslation vt) {
		mNextIndex = vt.mNextIndex;
		mVariables = new HashMap<TypedAbstractVariable, Variable>(vt.mVariables);
		mUID = sNextUID++;
	}

	/**
	 * 
	 */
	public HashMap<TypedAbstractVariable, Variable> getVariables() {
		return mVariables;
	}

	public int nofVariables() {
		return mVariables.size();
	}

	/**
	 * Adds a variable to the scope. The states dimensions must still be updated
	 * 
	 * @param variable
	 * @return
	 */
	public Variable addVariable(TypedAbstractVariable variable) {
		Variable x = new Variable(mNextIndex++);
		if (mVariables.containsKey(variable)) {
			throw new RuntimeException("Variable must not be declared twice");
		}

		// put it in the dictionary
		mVariables.put(variable, x);
		return x;
	}

	/**
	 * Removes a variable to the scope. The states dimensions must still be
	 * updated
	 * 
	 * @param variable
	 * @return
	 */
	public Variable removeVariable(TypedAbstractVariable variable) {
		Variable x = new Variable(mNextIndex++);
		if (mVariables.containsKey(variable)) {
			throw new RuntimeException("Variable must not be declared twice");
		}

		// put it in the dictionary
		mVariables.put(variable, x);
		return x;
	}

	/**
	 * Adds the given prefix to all variables.
	 * 
	 * @param prefix
	 */
	public void addPrefix(String prefix) {
		HashMap<TypedAbstractVariable, Variable> newVars = new HashMap<TypedAbstractVariable, Variable>();
		for (Entry<TypedAbstractVariable, Variable> var : mVariables.entrySet()) {
			TypedAbstractVariable tv = var.getKey();
			newVars.put(
					new TypedAbstractVariable(prefix + tv.getString(), tv
							.getDeclaration(), tv.getType()), var.getValue());
		}
		mVariables = newVars;
	}

	@Override
	public String toString() {
		String output = "[VT_" + mUID + " (#var: " + mNextIndex + ") ";
		String comma = "";
		for (Entry<TypedAbstractVariable, Variable> entry : mVariables
				.entrySet()) {
			output += comma + entry.getKey().getString() + " -> "
					+ entry.getValue().toString();
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
		for (Entry<TypedAbstractVariable, Variable> entry : mVariables
				.entrySet()) {
			Variable other = variableTranslation.getVariables().get(
					entry.getKey());
			if (other == null || entry.getValue().id() != other.id()) {
				return false;
			}
		}
		for (Entry<TypedAbstractVariable, Variable> entry : variableTranslation
				.getVariables().entrySet()) {
			Variable other = mVariables.get(entry.getKey());
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
		for (Entry<TypedAbstractVariable, Variable> entry : mVariables
				.entrySet()) {
			Variable otherVar = other.getVariables().get(entry.getKey());
			// if not existing
			if (otherVar == null) {
				other.getVariables().put(entry.getKey(), entry.getValue());
			} else if (entry.getValue().id() != otherVar.id()) {
				return false;
			}
		}

		// other to this
		for (Entry<TypedAbstractVariable, Variable> entry : other
				.getVariables().entrySet()) {
			Variable thisVar = mVariables.get(entry.getKey());
			// if not existing
			if (thisVar == null) {
				mVariables.put(entry.getKey(), entry.getValue());
			} else if (entry.getValue().id() != thisVar.id()) {
				return false;
			}
		}
		return true;
	}

	// /**
	// * Removes the given prefix from all variables
	// * @param prefix
	// */
	// public void removePrefix(String prefix)
	// {
	// HashMap<TypedAbstractVariable, Variable> newVars = new
	// HashMap<TypedAbstractVariable, Variable>();
	// for(Entry<TypedAbstractVariable, Variable> var : mVariables.entrySet())
	// {
	// TypedAbstractVariable tv = var.getKey();
	// String s = tv.getString();
	// if(s.startsWith(prefix))
	// {
	// s = s.substring(prefix.length());
	// }
	// newVars.put(new TypedAbstractVariable(s, tv.getDeclaration(),
	// tv.getType()), var.getValue());
	// }
	// mVariables = newVars;
	// }
}
