package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;
import parma_polyhedra_library.NNC_Polyhedron;
import parma_polyhedra_library.Partial_Function;
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
	private Map<Long, TypedAbstractVariable> mPPLVars2Vars;

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

	public long size() {
		return (mNextIndex);
	}

	/**
	 * Adds a variable to the scope. The states dimensions must still be updated
	 * 
	 * @param variable
	 * @return
	 */
	public Variable addVariable(TypedAbstractVariable variable) {
		return add(variable, mNextIndex);
	}

	public Variable addShiftedVariable(TypedAbstractVariable variable, long dimension) {
		return add(variable, dimension);
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
		final Map<Long, TypedAbstractVariable> newPPLVar2Var = new HashMap<>();
		for (Entry<TypedAbstractVariable, Variable> entry : mVars2PPLVars.entrySet()) {
			final TypedAbstractVariable oldtypedvar = entry.getKey();
			final TypedAbstractVariable newtypedvar = new TypedAbstractVariable(prefix + oldtypedvar.getString(),
					oldtypedvar.getDeclaration(), oldtypedvar.getType());

			newVar2PPLVar.put(newtypedvar, entry.getValue());
			newPPLVar2Var.put(entry.getValue().id(), newtypedvar);
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
		output += " | ";
		comma = "";
		for (Entry<Long, TypedAbstractVariable> entry : mPPLVars2Vars.entrySet()) {
			output += comma + new Variable(entry.getKey()).toString() + " -> " + entry.getValue().getString();
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

		// check if union is possible
		// from this to other
		for (Entry<TypedAbstractVariable, Variable> entry : mVars2PPLVars.entrySet()) {
			TypedAbstractVariable thisVar = entry.getKey();
			long thisPPLVAR = entry.getValue().id();			
			Variable otherPPLVar = other.mVars2PPLVars.get(thisVar);
			// check if thisVar is not assigned to a different ppl var
			if (otherPPLVar != null && entry.getValue().id() != otherPPLVar.id()) {
				return false;
			}
			// check that no other var is assigned to this ppl var
			TypedAbstractVariable otherVar = other.mPPLVars2Vars.get(thisPPLVAR);
			if (otherVar != null && !entry.getKey().equals(otherVar)) {
				return false;
			}
		}

	
		// ==> no overlap/possible
		// add missing ones at both sides
		// from this to other
		for (Entry<TypedAbstractVariable, Variable> entry : mVars2PPLVars.entrySet()) {
			Variable otherVar = other.mVars2PPLVars.get(entry.getKey());
			// if not existing
			if (otherVar == null) {
				other.add(entry.getKey(), entry.getValue().id());
			} 
		}

		// other to this
		for (Entry<TypedAbstractVariable, Variable> entry : other.mVars2PPLVars.entrySet()) {
			Variable thisVar = mVars2PPLVars.get(entry.getKey());
			// if not existing
			if (thisVar == null) {
				add(entry.getKey(), entry.getValue().id());
			} 
		}

		return true;
	}

	public TypedAbstractVariable checkVar(Object variable) {
		// TODO: This construct is here because JH handles scoping in a
		// monstrous way (and wrong). Ask DD if you want to hear him rant for
		// 30mins.
		for (TypedAbstractVariable tav : mVars2PPLVars.keySet()) {
			if (tav.equals(variable)) {
				return tav;
			}
		}
		return null;
	}

	public Variable getPPLVar(Object variable) {
		return mVars2PPLVars.get(variable);
	}

	private Variable add(TypedAbstractVariable var, long index) {
		Variable pplvar = mVars2PPLVars.get(var);
		if (pplvar == null) {
			assert index >= mNextIndex;
			pplvar = new Variable(index);
			mNextIndex = Math.max(mNextIndex, index + 1);
			mVars2PPLVars.put(var, pplvar);
			mPPLVars2Vars.put(pplvar.id(), var);
		}
		return pplvar;
	}

	public TypedAbstractVariable getVar(Variable arg) {
		TypedAbstractVariable rtr = mPPLVars2Vars.get(arg.id());
		if (rtr != null) {
			return rtr;
		}
		String str = arg.toString();
		for (Entry<Long, TypedAbstractVariable> entry : mPPLVars2Vars.entrySet()) {
			if (entry.getKey().equals(arg)) {
				return entry.getValue();
			} else if (entry.getKey().toString().equals(str)) {
				return entry.getValue();
			}
		}
		return null;
	}

	public Partial_Function remap(VariableTranslation other, Logger logger) {
		Partial_Function mapping = new Partial_Function();

		mNextIndex = Math.max(mNextIndex, other.mNextIndex);
		for (Entry<TypedAbstractVariable, Variable> var2PPLVar : mVars2PPLVars.entrySet()) {
			TypedAbstractVariable thisVar = var2PPLVar.getKey();
			Variable thisPPLVar = var2PPLVar.getValue();
			Variable otherPPLVar = other.mVars2PPLVars.get(var2PPLVar.getKey());
			// if existing but assigned otherwise, map to the same as in other
			if (otherPPLVar != null && otherPPLVar.id() != thisPPLVar.id()) {
				
				// if this was already taken, ...
				TypedAbstractVariable oldVar = mPPLVars2Vars.get(otherPPLVar.id());
				if (oldVar != null) {
					// check if the variable exists in the other
					// if not re-map it to something new
					if (!other.mVars2PPLVars.containsKey(oldVar)) {
						logger.debug("map: " + otherPPLVar + "("+otherPPLVar.id()+") -> " + new Variable(mNextIndex) + "("+mNextIndex+")");
						mapping.insert(otherPPLVar.id(), mNextIndex);
						mNextIndex++;
					}
				}
				
				mapping.insert(thisPPLVar.id(), otherPPLVar.id());				
				logger.debug("map: " + thisPPLVar + "("+thisPPLVar.id()+") -> " + otherPPLVar + "("+otherPPLVar.id()+")");
				
			}
		}
		logger.debug(mapping.has_empty_codomain());

		// apply the mapping
		// var -> ppl
		for (Entry<TypedAbstractVariable, Variable> entry : mVars2PPLVars.entrySet()) {
			long newId = mapping.maps(entry.getValue().id());
			if (newId > -1) {
				mNextIndex = Math.max(mNextIndex, newId + 1);

				Variable newVar = new Variable(newId);
				logger.debug("put " + entry.getKey() + " to " + newVar);
				mVars2PPLVars.put(entry.getKey(), newVar);
			}
		}
		// ppl -> var
		mPPLVars2Vars = new HashMap<Long, TypedAbstractVariable>();
		for (Entry<TypedAbstractVariable, Variable> entry : mVars2PPLVars.entrySet()) {
			logger.debug("put " + entry.getValue() + " to " + entry.getKey());
			mPPLVars2Vars.put(entry.getValue().id(), entry.getKey());
		}

		return mapping;
	}
}
