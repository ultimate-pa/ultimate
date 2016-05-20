/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;

/**
 * Factory for constructing ReplacementVars ensures that for each defining
 * Term exactly one ReplacementVar is constructed.
 * @author Matthias Heizmann
 *
 */
public class ReplacementVarFactory {
	
	private final IFreshTermVariableConstructor m_VariableManager;
	private final Map<Term, ReplacementVar> m_RepVarMapping = 
			new HashMap<Term, ReplacementVar>();
	private final Map<Term, Map<Object, LocalReplacementVar>> m_LocalRepVarMapping = 
			new HashMap<Term, Map<Object, LocalReplacementVar>>();
	private final Map<String, TermVariable> m_AuxVarMapping = 
			new HashMap<String, TermVariable>();
	/**
	 * Maps each BoogieVar to a unique BoogieVarWrapper.
	 */
	private final Map<BoogieVar, BoogieVarWrapper> m_BoogieVarWrappers
		= new HashMap<BoogieVar, BoogieVarWrapper>();

	public ReplacementVarFactory(IFreshTermVariableConstructor variableManager) {
		super();
		m_VariableManager = variableManager;
	}

	/**
	 * Get the ReplacementVar that is used as a replacement for the Term
	 * definition. Construct this ReplacementVar if it does not exist yet.
	 */
	public ReplacementVar getOrConstuctReplacementVar(Term definition) {
		ReplacementVar repVar = m_RepVarMapping.get(definition);
		if (repVar == null) {
			repVar = new ReplacementVar(definition.toString(), definition);
			m_RepVarMapping.put(definition, repVar);
		}
		return repVar;
	}
	
	/**
	 * Get the LocalReplacementVar that is used as a replacement for the Term
	 * definition at the ProgramPoint location. 
	 * Construct this LocalReplacementVar if it does not exist yet.
	 */
	public ReplacementVar getOrConstuctLocalReplacementVar(Term definition, Object location) {
		Map<Object, LocalReplacementVar> locToRepVar = m_LocalRepVarMapping.get(definition);
		if (definition == null) {
			locToRepVar = new HashMap<Object, LocalReplacementVar>();
			m_LocalRepVarMapping.put(definition, locToRepVar);
		}
		LocalReplacementVar repVar = locToRepVar.get(location);
		if (repVar == null) {
			repVar = new LocalReplacementVar(definition.toString(), definition, location);
			locToRepVar.put(location, repVar);
		}
		return repVar;
	}

	
	/**
	 * Construct and return a unique TermVariable with the given name.
	 */
	public TermVariable getOrConstructAuxVar(String name, Sort sort) {
		TermVariable auxVar = m_AuxVarMapping.get(name);
		if (auxVar == null) {
			auxVar = m_VariableManager.constructFreshTermVariable(name, sort);
			m_AuxVarMapping.put(name, auxVar);
		} else {
			if (sort != auxVar.getSort()) {
				throw new AssertionError("cannot construct auxVars with same name and different sort");
			}
		}
		return auxVar;
	}
	
	
	/**
	 * Get unique BoogieVarWrapper for a given BoogieVar.
	 */
	public RankVar getOrConstuctBoogieVarWrapper(BoogieVar boogieVar) {
		if (m_BoogieVarWrappers.containsKey(boogieVar)) {
			return m_BoogieVarWrappers.get(boogieVar);
		} else {
			BoogieVarWrapper wrapper = new BoogieVarWrapper(boogieVar);
			m_BoogieVarWrappers.put(boogieVar, wrapper);
			return wrapper;
		}
	}

}
