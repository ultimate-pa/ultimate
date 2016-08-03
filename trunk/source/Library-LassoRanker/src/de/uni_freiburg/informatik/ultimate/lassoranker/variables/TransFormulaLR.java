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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;


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
 * @see RankVar
 */
public class TransFormulaLR implements Serializable {
	private static final long serialVersionUID = -1005909010259944923L;
	
	private final Map<RankVar, Term> minVars;
	private final Map<Term, RankVar> minVarsReverseMapping;
	private final Map<RankVar, Term> moutVars;
	private final Map<Term, RankVar> moutVarsReverseMapping;
	private final Map<TermVariable, Term> mAuxVars;
	
	private Term mformula;
	
	/**
	 * Create a new TransformulaLR
	 * @param formula the transition formula
	 */
	TransFormulaLR(Term formula) {
		minVars = new LinkedHashMap<RankVar, Term>();
		minVarsReverseMapping = new LinkedHashMap<Term, RankVar>();
		moutVars = new LinkedHashMap<RankVar, Term>();
		moutVarsReverseMapping = new LinkedHashMap<Term, RankVar>();
		mAuxVars = new HashMap<TermVariable, Term>();
		mformula = formula;
	}
	
	/**
	 * Copy constructor
	 */
	public TransFormulaLR(TransFormulaLR other) {
		this(other.getFormula());
		minVars.putAll(other.minVars);
		minVarsReverseMapping.putAll(other.minVarsReverseMapping);
		moutVars.putAll(other.moutVars);
		moutVarsReverseMapping.putAll(other.moutVarsReverseMapping);
		mAuxVars.putAll(other.getAuxVars());
	}
	
	
	/**
	 * Construct a TransFormulaLR from a TransFormula, adding and translating
	 * all existing in- and outVars in the process.
	 * @param transition the TransFormula
	 */
	public static TransFormulaLR buildTransFormula(TransFormula transition,
			ReplacementVarFactory replacementVarFactory) {
		final TransFormulaLR tf = new TransFormulaLR(transition.getFormula());
		
		// Add existing in- and outVars
		for (final Map.Entry<IProgramVar, TermVariable> entry
				: transition.getInVars().entrySet()) {
			tf.addInVar(replacementVarFactory.getOrConstuctBoogieVarWrapper(
					entry.getKey()), entry.getValue());
		}
		for (final Map.Entry<IProgramVar, TermVariable> entry
				: transition.getOutVars().entrySet()) {
			tf.addOutVar(replacementVarFactory.getOrConstuctBoogieVarWrapper(
					entry.getKey()), entry.getValue());
		}
		tf.addAuxVars(transition.getAuxVars());
		
		// Add constant variables as in- and outVars
		for (final ApplicationTerm constVar : transition.getConstants()) {
			final ReplacementVar repVar = 
					replacementVarFactory.getOrConstuctReplacementVar(constVar); 
			tf.addInVar(repVar, constVar);
			tf.addOutVar(repVar, constVar);
		}
		return tf;
	}
	
	/**
	 * @return the collected inVars
	 */
	public Map<RankVar, Term> getInVars() {
		return Collections.unmodifiableMap(minVars);
	}
	
	/**
	 * @return mapping from inVars to the RankVar that is represented by the
	 * inVar
	 */
	public Map<Term, RankVar> getInVarsReverseMapping() {
		return Collections.unmodifiableMap(minVarsReverseMapping);
	}

	/**
	 * @return the collected outVars
	 */
	public Map<RankVar, Term> getOutVars() {
		return Collections.unmodifiableMap(moutVars);
	}
	
	/**
	 * @return mapping from outVars to the RankVar that is represented by the
	 * outVar
	 */
	public Map<Term, RankVar> getOutVarsReverseMapping() {
		return Collections.unmodifiableMap(moutVarsReverseMapping);
	}
	
	/**
	 * @return the collected auxVars
	 */
	public Map<TermVariable, Term> getAuxVars() {
		return Collections.unmodifiableMap(mAuxVars);
	}
	
	/**
	 * Add an inVar to the collection
	 * @param rkVar a RankVar
	 * @param var the TermVariable corresponding to the RankVar's input state
	 *            (unprimed version)
	 */
	public void addInVar(RankVar rkVar, Term var) {
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
	public void removeInVar(RankVar rkVar) {
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
	public void addOutVar(RankVar rkVar, Term var) {
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
	public void removeOutVar(RankVar rkVar) {
		final Term tv = moutVars.remove(rkVar);
		if (tv == null) {
			throw new AssertionError(
					"cannot remove variable that is not contained");
		} else {
			moutVarsReverseMapping.remove(tv);
		}
	}
	
	public void removeAuxVar(TermVariable auxVar) {
		final Term oldValue = mAuxVars.remove(auxVar);
		if (oldValue == null) {
			throw new AssertionError(
					"cannot remove variable that is not contained");
		}
	}
	
	
	/**
	 * Add a TermVariables that each neither occur as inVar or outVar to the set
	 * of auxiliary variables. (Note that auxiliary variables are different from
	 * replacement variables).
	 */
	public void addAuxVars(Map<TermVariable, Term> auxVars) {
		mAuxVars.putAll(auxVars);
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
	public void setFormula(Term formula) {
		mformula = formula;
	}
	
	/**
	 * Returns true if each auxVar occurs neither as inVar nor as outVar.
	 * This property should always hold.
	 */
	public boolean auxVarsDisjointFromInOutVars() {
		for (final Term auxVar : mAuxVars.keySet()) {
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
	public TermVariable allAreInOutAux(TermVariable[] tvs) {
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
	private HashSet<RankVar> computeAssignedVars() {
		final HashSet<RankVar> assignedVars = new HashSet<RankVar>();
		for (final RankVar var : moutVars.keySet()) {
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
	public Set<RankVar> getAssignedVars() {
		return Collections.unmodifiableSet(computeAssignedVars());
	}
	
	/**
	 * @return whether the TermVariable tv occurs as inVar, outVar, or auxVar.
	 */
	private boolean isInOurAux(TermVariable tv) {
		if (minVarsReverseMapping.containsKey(tv)) {
			return true;
		} else if (moutVarsReverseMapping.containsKey(tv)) {
			return true;
		} else if (mAuxVars.keySet().contains(tv)) {
			return true;
		} else {
			return false;
		}
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
