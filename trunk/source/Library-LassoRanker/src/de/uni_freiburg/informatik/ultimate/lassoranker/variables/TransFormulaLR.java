/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.variables;

import java.io.Serializable;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.SMTPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


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
 * @author Jan Leike, Matthias Heizmann
 * 
 * @see VarFactory
 * @see RankVar
 */
public class TransFormulaLR implements Serializable {
	private static final long serialVersionUID = -1005909010259944923L;
	
	private final Map<RankVar, Term> m_inVars;
	private final Map<Term, RankVar> m_inVarsReverseMapping;
	private final Map<RankVar, Term> m_outVars;
	private final Map<Term, RankVar> m_outVarsReverseMapping;
	private final Set<TermVariable> m_AuxVars;
	
	private Term m_formula;
	
	/**
	 * Create a new TransformulaLR
	 * @param formula the transition formula
	 */
	TransFormulaLR(Term formula) {
		m_inVars = new LinkedHashMap<RankVar, Term>();
		m_inVarsReverseMapping = new LinkedHashMap<Term, RankVar>();
		m_outVars = new LinkedHashMap<RankVar, Term>();
		m_outVarsReverseMapping = new LinkedHashMap<Term, RankVar>();
		m_AuxVars = new HashSet<TermVariable>();
		m_formula = formula;
	}
	
	/**
	 * Copy constructor
	 */
	public TransFormulaLR(TransFormulaLR other) {
		this(other.getFormula());
		m_inVars.putAll(other.m_inVars);
		m_inVarsReverseMapping.putAll(other.m_inVarsReverseMapping);
		m_outVars.putAll(other.m_outVars);
		m_outVarsReverseMapping.putAll(other.m_outVarsReverseMapping);
		m_AuxVars.addAll(other.getAuxVars());
	}
	
	/**
	 * @return the collected inVars
	 */
	public Map<RankVar, Term> getInVars() {
		return Collections.unmodifiableMap(m_inVars);
	}
	
	/**
	 * @return mapping from inVars to the RankVar that is represented by the
	 * inVar
	 */
	public Map<Term, RankVar> getInVarsReverseMapping() {
		return Collections.unmodifiableMap(m_inVarsReverseMapping);
	}

	/**
	 * @return the collected outVars
	 */
	public Map<RankVar, Term> getOutVars() {
		return Collections.unmodifiableMap(m_outVars);
	}
	
	/**
	 * @return mapping from outVars to the RankVar that is represented by the
	 * outVar
	 */
	public Map<Term, RankVar> getOutVarsReverseMapping() {
		return Collections.unmodifiableMap(m_outVarsReverseMapping);
	}
	
	/**
	 * @return the collected auxVars
	 */
	public Set<TermVariable> getAuxVars() {
		return Collections.unmodifiableSet(m_AuxVars);
	}
	
	/**
	 * Add an inVar to the collection
	 * @param rkVar a RankVar
	 * @param var the TermVariable corresponding to the RankVar's input state
	 *            (unprimed version)
	 */
	public void addInVar(RankVar rkVar, Term var) {
		assert !m_inVars.containsKey(rkVar);
		m_inVars.put(rkVar, var);
		m_inVarsReverseMapping.put(var, rkVar);
	}
	
	/**
	 * Remove an inVar from the collection
	 */
	public void removeInVar(RankVar rkVar) {
		Term tv = m_inVars.remove(rkVar);
		if (tv == null) {
			throw new AssertionError(
					"cannot remove variable that is not contained");
		} else {
			m_inVarsReverseMapping.remove(tv);
		}
	}
	
	/**
	 * Add an outVar to the collection
	 * @param rkVar a RankVar
	 * @param var the TermVariable corresponding to the RankVar's output state
	 *            (primed version)
	 */
	public void addOutVar(RankVar rkVar, Term var) {
		assert !m_outVars.containsKey(rkVar);
		m_outVars.put(rkVar, var);
		m_outVarsReverseMapping.put(var, rkVar);
	}
	
	/**
	 * Remove an outVar from the collection
	 */
	public void removeOutVar(RankVar rkVar) {
		Term tv = m_outVars.remove(rkVar);
		if (tv == null) {
			throw new AssertionError(
					"cannot remove variable that is not contained");
		} else {
			m_outVarsReverseMapping.remove(tv);
		}
	}
	
	
	/**
	 * Add a TermVariables that each neither occur as inVar or outVar to the set
	 * of auxiliary variables. (Note that auxiliary variables are different from
	 * replacement variables).
	 */
	public void addAuxVars(Collection<TermVariable> auxVars) {
		m_AuxVars.addAll(auxVars);
	}
	
	/**
	 * @return the transition formula
	 */
	public Term getFormula() {
		return m_formula;
	}
	
	/**
	 * @param term the new transition formula
	 */
	public void setFormula(Term formula) {
		m_formula = formula;
	}
	
	/**
	 * Returns true if each auxVar occurs neither as inVar nor as outVar.
	 * This property should always hold.
	 */
	public boolean auxVarsDisjointFromInOutVars() {
		for (Term auxVar : m_AuxVars) {
			if (m_inVarsReverseMapping.containsKey(auxVar)) {
				return false;
			}
			if (m_outVarsReverseMapping.containsKey(auxVar)) {
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
		for (TermVariable tv : tvs) {
			if (!isInOurAux(tv)) {
				return tv;
			}
		}
		return null;
	}
	
	/**
	 * @return whether the TermVariable tv occurs as inVar, outVar, or auxVar.
	 */
	private boolean isInOurAux(TermVariable tv) {
		if (m_inVarsReverseMapping.containsKey(tv)) {
			return true;
		} else if (m_outVarsReverseMapping.containsKey(tv)) {
			return true;
		} else if (m_AuxVars.contains(tv)) {
			return true;
		} else {
			return false;
		}
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("InVars: ");
		sb.append(m_inVars.toString());
		sb.append("\nOutVars: ");
		sb.append(m_outVars.toString());
		sb.append("\nAuxVars: ");
		sb.append(m_AuxVars.toString());
		sb.append("\nTransition formula: ");
		sb.append(new SMTPrettyPrinter(m_formula));
		return sb.toString();
	}
}
