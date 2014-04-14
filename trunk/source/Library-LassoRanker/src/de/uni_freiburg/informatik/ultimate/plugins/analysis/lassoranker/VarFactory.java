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
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableManager;

/**
 * Used to create and manage RankVars and auxiliary variables.
 * The RankVars created through this class are properly unique.
 * 
 * @author Jan Leike
 */
public class VarFactory implements Serializable {
	private static final long serialVersionUID = 7278586799569746241L;
	
	/**
	 * The VariableManager associated with the Boogie2SMT
	 */
	private final VariableManager m_varManager;
	
	/**
	 * Table of the created BoogieVarWrapper's such that every BoogieVar
	 * gets at most one wrapper
	 */
	private final Map<BoogieVar, BoogieVarWrapper> m_boogieWrappers;
	
	/**
	 * The map indexing replacement variables registered with this object
	 */
	private final Map<Object, ReplacementVar> m_repVars;
	
	/**
	 * Collection of all generated replacement TermVariables
	 */
	private final Collection<TermVariable> m_termVariables;
	
	/**
	 * 
	 * @param boogie2smt
	 */
	public VarFactory(Boogie2SMT boogie2smt) {
		assert boogie2smt != null;
		m_varManager = boogie2smt.getVariableManager();
		m_boogieWrappers = new LinkedHashMap<BoogieVar, BoogieVarWrapper>();
		m_repVars = new LinkedHashMap<Object, ReplacementVar>();
		m_termVariables = new ArrayList<TermVariable>();
	}
	
	/**
	 * @return a collection of all new TermVariable's created with this object
	 */
	public Collection<TermVariable> getGeneratedTermVariables() {
		return Collections.unmodifiableCollection(m_termVariables);
	}
	
	/**
	 * Wrap BoogieVar's in a one-to-one fashion
	 */
	public RankVar fromBoogieVar(BoogieVar boogieVar) {
		if (m_boogieWrappers.containsKey(boogieVar)) {
			return m_boogieWrappers.get(boogieVar);
		} else {
			BoogieVarWrapper wrapper = new BoogieVarWrapper(boogieVar);
			m_boogieWrappers.put(boogieVar, wrapper);
			return wrapper;
		}
	}
	
	/**
	 * Register a replacement variable to be unique for this factory
	 * @param key a key to store repVar with
	 * @param repVar the replacement variable to be stored 
	 */
	public void registerRepVar(Object key, ReplacementVar repVar) {
		assert !m_repVars.containsKey(key);
		m_repVars.put(key, repVar);
	}
	
	/**
	 * Fetch a previously stored replacement variable
	 * @param key the key used to store the repVar
	 * @return the repVar
	 */
	public ReplacementVar getRepVar(Object key) {
		return m_repVars.get(key);
	}
	
	/**
	 * Construct and return a unique term variable with the given name.
	 * The new variable has the same sort as the given Term definition.
	 * @param name an identifier for the variable
	 * @param definition a term that new variable is replacing
	 */
	public TermVariable getNewTermVariable(String name, Sort sort) {
		TermVariable newVar =
				m_varManager.constructFreshTermVariable(name, sort);
		m_termVariables.add(newVar);
		return newVar;
	}
}
