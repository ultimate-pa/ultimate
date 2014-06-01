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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.io.Serializable;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;


/**
 * Object that stores
 * <ul> 
 * <li> a mapping between inVars and RankVars,
 * <li> a mapping between outVars and RankVars, and
 * <li> a set of auxiliary variables.
 * Together with a term whose free variables are the inVars, ourVars and 
 * auxVars, this object defines a transition relation.
 * 
 * @author Jan Leike, Matthias Heizmann
 * 
 * @see VarFactory
 * @see RankVar
 */
public class VarCollector implements Serializable {
	private static final long serialVersionUID = -1005909010259944923L;
	
	private final Map<RankVar, TermVariable> m_inVars;
	private final Map<TermVariable, RankVar> m_inVarsReverseMapping;
	private final Map<RankVar, TermVariable> m_outVars;
	private final Map<TermVariable, RankVar> m_outVarsReverseMapping;
	private final Set<TermVariable> m_AuxVars;
	private final VarFactory m_factory;
	
	/**
	 * Create a new VarCollector
	 * @param factory the VarFactory to be used for creating RankVars
	 */
	public VarCollector(VarFactory factory) {
		assert factory != null;
		m_inVars = new LinkedHashMap<RankVar, TermVariable>();
		m_inVarsReverseMapping = new LinkedHashMap<TermVariable, RankVar>();
		m_outVars = new LinkedHashMap<RankVar, TermVariable>();
		m_outVarsReverseMapping = new LinkedHashMap<TermVariable, RankVar>();
		m_AuxVars = new HashSet<TermVariable>();
		m_factory = factory;
	}
	
	/**
	 * Construct a VarCollector from a TransFormula, adding and translating
	 * all existing in- and outVars in the process.
	 * @param factory the VarFactory to be used for creating RankVars
	 * @param transition for extracting in- and outVars
	 */
	public VarCollector(VarFactory factory, TransFormula transition) {
		this(factory);
		
		// Add existing in- and outVars
		for (Map.Entry<BoogieVar, TermVariable> entry
				: transition.getInVars().entrySet()) {
			addInVar(m_factory.fromBoogieVar(entry.getKey()),
					entry.getValue());
		}
		for (Map.Entry<BoogieVar, TermVariable> entry
				: transition.getOutVars().entrySet()) {
			addOutVar(m_factory.fromBoogieVar(entry.getKey()),
					entry.getValue());
		}
		for (TermVariable auxVar : transition.getAuxVars()) {
			m_AuxVars.add(auxVar);
		}
	}
	
	/**
	 * @return the collected inVars
	 */
	public Map<RankVar, TermVariable> getInVars() {
		return Collections.unmodifiableMap(m_inVars);
	}
	
	/**
	 * @return the collected outVars
	 */
	public Map<RankVar, TermVariable> getOutVars() {
		return Collections.unmodifiableMap(m_outVars);
	}
	
	public Set<TermVariable> getAuxVars() {
		return Collections.unmodifiableSet(m_AuxVars);
	}
	
	/**
	 * @return the associated VarFactory
	 */
	public VarFactory getFactory() {
		return m_factory;
	}
	
	/**
	 * Add an inVar to the collection
	 * @param rkVar a RankVar
	 * @param var the TermVariable corresponding to the RankVar's input state
	 *            (unprimed version)
	 */
	public void addInVar(RankVar rkVar, TermVariable var) {
		m_inVars.put(rkVar, var);
		m_inVarsReverseMapping.put(var, rkVar);
	}
	
	/**
	 * Remove an inVar from the collection
	 */
	public void removeInVar(RankVar rkVar) {
		TermVariable tv = m_inVars.remove(rkVar);
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
	public void addOutVar(RankVar rkVar, TermVariable var) {
		m_outVars.put(rkVar, var);
		m_outVarsReverseMapping.put(var, rkVar);
	}
	
	/**
	 * Remove an outVar from the collection
	 */
	public void removeOutVar(RankVar rkVar) {
		TermVariable tv = m_outVars.remove(rkVar);
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
	 * Add a corresponding inVar for all outVars.
	 * 
	 * This is required to prevent a problem that was reported by Matthias
	 * in Madrid.bpl. This problem occurs when there are outVars that do not
	 * have a corresponding inVar. Supporting invariant generation then becomes
	 * unsound for the inductiveness property.
	 */
	public void matchInVars() {
		for (Map.Entry<RankVar, TermVariable> entry : m_outVars.entrySet()) {
			if (!m_inVars.containsKey(entry.getKey())) {
				TermVariable inVar = m_factory.getNewTermVariable(
						entry.getKey().getGloballyUniqueId(),
						entry.getValue().getSort()
				);
				addInVar(entry.getKey(), inVar);
			}
		}
	}
	
	/**
	 * Returns true if each auxVar occurs neither as inVar nor as outVar.
	 * This property should always hold.
	 */
	public boolean auxVarsDisjointFormInOutVars() {
		for (TermVariable auxVar : m_AuxVars) {
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
	 * Return true iff the TermVariable tv occurs as inVar as outVar or as
	 * auxVar.
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
		return sb.toString();
	}
}
