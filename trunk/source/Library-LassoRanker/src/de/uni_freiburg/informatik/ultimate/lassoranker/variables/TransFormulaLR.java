/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.variables;

import java.io.Serializable;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.SMTPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;


/**
 * This class stores
 * <ul>
 * <li> a mapping between inVars and RankVars,
 * <li> a mapping between outVars and RankVars, and
 * <li> a set of auxiliary variables.
 * <li> a transition formula (Term)
 * </ul>
 * 
 * It is similar to TransFormula, and there are hopes that on some glorious
 * future day the two classes shall become one. LR stands for LassoRanker.
 * 
 * This object is *not* immutable.
 * 
 * @author Jan Leike
 * @author Matthias Heizmann
 * 
 * @see VarFactory
 * @see IProgramVar
 */
public class TransFormulaLR implements Serializable {
	private static final long serialVersionUID = -1005909010259944923L;
	
	private final Map<IProgramVar, Term> minVars;
	private final Map<Term, IProgramVar> minVarsReverseMapping;
	private final Map<IProgramVar, Term> moutVars;
	private final Map<Term, IProgramVar> moutVarsReverseMapping;
	private final Set<TermVariable> mAuxVars;
	
	private Term mformula;
	
	/**
	 * Create a new TransformulaLR
	 * @param formula the transition formula
	 */
	TransFormulaLR(final Term formula) {
		minVars = new LinkedHashMap<IProgramVar, Term>();
		minVarsReverseMapping = new LinkedHashMap<Term, IProgramVar>();
		moutVars = new LinkedHashMap<IProgramVar, Term>();
		moutVarsReverseMapping = new LinkedHashMap<Term, IProgramVar>();
		mAuxVars = new HashSet<TermVariable>();
		mformula = formula;
	}
	
	/**
	 * Copy constructor
	 */
	public TransFormulaLR(final TransFormulaLR other) {
		this(other.getFormula());
		minVars.putAll(other.minVars);
		minVarsReverseMapping.putAll(other.minVarsReverseMapping);
		moutVars.putAll(other.moutVars);
		moutVarsReverseMapping.putAll(other.moutVarsReverseMapping);
		mAuxVars.addAll(other.getAuxVars());
	}
	
	
	/**
	 * Construct a TransFormulaLR from a TransFormula, adding and translating
	 * all existing in- and outVars in the process.
	 * @param oldTf the TransFormula
	 */
	public static TransFormulaLR buildTransFormula(final UnmodifiableTransFormula oldTf,
			final ReplacementVarFactory replacementVarFactory, final ManagedScript mgdScript) {
		// construct copies of auxVars
		final Set<TermVariable> auxVars = new HashSet<>();
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final TermVariable auxVar : oldTf.getAuxVars()) {
			final TermVariable newAuxVar = mgdScript.constructFreshCopy(auxVar);
			auxVars.add(newAuxVar);
			substitutionMapping.put(auxVar, newAuxVar);
		}
		final TransFormulaLR newTf = new TransFormulaLR(
				(new Substitution(mgdScript, substitutionMapping).transform(oldTf.getFormula())));
		
		// Add existing in- and outVars
		for (final Map.Entry<IProgramVar, TermVariable> entry
				: oldTf.getInVars().entrySet()) {
			newTf.addInVar(entry.getKey(), entry.getValue());
		}
		for (final Map.Entry<IProgramVar, TermVariable> entry
				: oldTf.getOutVars().entrySet()) {
			newTf.addOutVar(entry.getKey(), entry.getValue());
		}
		newTf.addAuxVars(auxVars);
		
		// Add constant variables as in- and outVars
		for (final ApplicationTerm constVar : oldTf.getConstants()) {
			final ReplacementVar repVar =
					replacementVarFactory.getOrConstuctReplacementVar(constVar);
			newTf.addInVar(repVar, constVar);
			newTf.addOutVar(repVar, constVar);
		}
		return newTf;
	}
	
	/**
	 * @return the collected inVars
	 */
	public Map<IProgramVar, Term> getInVars() {
		return Collections.unmodifiableMap(minVars);
	}
	
	/**
	 * @return mapping from inVars to the RankVar that is represented by the
	 * inVar
	 */
	public Map<Term, IProgramVar> getInVarsReverseMapping() {
		return Collections.unmodifiableMap(minVarsReverseMapping);
	}

	/**
	 * @return the collected outVars
	 */
	public Map<IProgramVar, Term> getOutVars() {
		return Collections.unmodifiableMap(moutVars);
	}
	
	/**
	 * @return mapping from outVars to the RankVar that is represented by the
	 * outVar
	 */
	public Map<Term, IProgramVar> getOutVarsReverseMapping() {
		return Collections.unmodifiableMap(moutVarsReverseMapping);
	}
	
	/**
	 * @return the collected auxVars
	 */
	public Set<TermVariable> getAuxVars() {
		return Collections.unmodifiableSet(mAuxVars);
	}
	
	/**
	 * Add an inVar to the collection
	 * @param rkVar a RankVar
	 * @param var the TermVariable corresponding to the RankVar's input state
	 *            (unprimed version)
	 */
	public void addInVar(final IProgramVar rkVar, final Term var) {
		final Term oldValue = minVars.put(rkVar, var);
		if (oldValue == null) {
			minVarsReverseMapping.put(var, rkVar);
		} else {
			if (oldValue != var) {
				throw new IllegalArgumentException(
						oldValue + " is already the inVar of " + rkVar);
			}
		}
	}
	
	/**
	 * Remove an inVar from the collection
	 */
	public void removeInVar(final IProgramVar rkVar) {
		final Term tv = minVars.remove(rkVar);
		if (tv == null) {
			throw new AssertionError(
					"cannot remove variable that is not contained");
		} else {
			minVarsReverseMapping.remove(tv);
		}
	}
	
	/**
	 * Add an outVar to the collection
	 * @param rkVar a RankVar
	 * @param var the TermVariable corresponding to the RankVar's output state
	 *            (primed version)
	 */
	public void addOutVar(final IProgramVar rkVar, final Term var) {
		final Term oldValue = moutVars.put(rkVar, var);
		if (oldValue == null) {
			moutVarsReverseMapping.put(var, rkVar);
		} else {
			if (oldValue != var) {
				throw new IllegalArgumentException(
						oldValue + " is already the outVar of " + rkVar);
			}
		}
	}
	
	/**
	 * Remove an outVar from the collection
	 */
	public void removeOutVar(final IProgramVar rkVar) {
		final Term tv = moutVars.remove(rkVar);
		if (tv == null) {
			throw new AssertionError(
					"cannot remove variable that is not contained");
		} else {
			moutVarsReverseMapping.remove(tv);
		}
	}
	
	public void removeAuxVar(final TermVariable auxVar) {
		final boolean modified = mAuxVars.remove(auxVar);
		if (!modified) {
			throw new AssertionError(
					"cannot remove variable that is not contained");
		}
	}
	
	
	/**
	 * Add a TermVariables that each neither occur as inVar or outVar to the set
	 * of auxiliary variables. (Note that auxiliary variables are different from
	 * replacement variables).
	 */
	public void addAuxVars(final Set<TermVariable> auxVars) {
		mAuxVars.addAll(auxVars);
	}
	
	/**
	 * @return the transition formula
	 */
	public Term getFormula() {
		return mformula;
	}
	
	/**
	 * @param term the new transition formula
	 */
	public void setFormula(final Term formula) {
		mformula = formula;
	}
	
	/**
	 * Returns true if each auxVar occurs neither as inVar nor as outVar.
	 * This property should always hold.
	 */
	public boolean auxVarsDisjointFromInOutVars() {
		for (final Term auxVar : mAuxVars) {
			if (minVarsReverseMapping.containsKey(auxVar)) {
				return false;
			}
			if (moutVarsReverseMapping.containsKey(auxVar)) {
				return false;
			}
		}
		return true;
	}
	
	/**
	 * Returns some TermVariable from tvs that occurs neither as inVar nor
	 * as outVar nor as auxVar. Returns null if no such TermVariable in tvs
	 * exists.
	 * For the variables that occur in the transition that uses this
	 * VarCollector the result should always be null.
	 */
	public TermVariable allAreInOutAux(final TermVariable[] tvs) {
		for (final TermVariable tv : tvs) {
			if (!isInOurAux(tv)) {
				return tv;
			}
		}
		return null;
	}
	
	/**
	 * compute the assigned/updated variables. A variable is updated by this
     * transition if it occurs as outVar and
     * - it does not occur as inVar
	 * - or the inVar is represented by a different TermVariable
	 */
	private HashSet<IProgramVar> computeAssignedVars() {
		final HashSet<IProgramVar> assignedVars = new HashSet<IProgramVar>();
		for (final IProgramVar var : moutVars.keySet()) {
			assert (moutVars.get(var) != null);
			if (moutVars.get(var) != minVars.get(var)) {
				assignedVars.add(var);
			}
		}
		return assignedVars;
	}
	
	/**
	 * @return the set of assigned/updated variables. A variable is updated by
	 * this transition if it occurs as outVar and
     * - it does not occur as inVar
	 * - or the inVar is represented by a different TermVariable
	 */
	public Set<IProgramVar> getAssignedVars() {
		return Collections.unmodifiableSet(computeAssignedVars());
	}
	
	/**
	 * @return whether the TermVariable tv occurs as inVar, outVar, or auxVar.
	 */
	private boolean isInOurAux(final TermVariable tv) {
		if (minVarsReverseMapping.containsKey(tv) || moutVarsReverseMapping.containsKey(tv)) {
			return true;
		}
		return mAuxVars.contains(tv);
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("InVars: ");
		sb.append(minVars.toString());
		sb.append("\nOutVars: ");
		sb.append(moutVars.toString());
		sb.append("\nAuxVars: ");
		sb.append(mAuxVars.toString());
		sb.append("\nTransition formula: ");
		sb.append(new SMTPrettyPrinter(mformula));
		return sb.toString();
	}
}
