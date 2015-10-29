/*
 * Copyright (C) 2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.AbstractMap;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

/**
 * 
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class PredicateFactoryForInterpolantConsolidation extends PredicateFactory {
	
	private Map<IPredicate, Set<IPredicate>> m_LocationsToSetOfPredicates;
	private Map<IPredicate, AbstractMap.SimpleEntry<IPredicate, IPredicate>> m_IntersectedPredicateToArgumentPredicates;
	public PredicateFactoryForInterpolantConsolidation(SmtManager smtManager,
			TAPreferences taPrefs) {
		super(smtManager, taPrefs);
		m_LocationsToSetOfPredicates = new HashMap<IPredicate, Set<IPredicate>>();
		m_IntersectedPredicateToArgumentPredicates = new HashMap<IPredicate, AbstractMap.SimpleEntry<IPredicate, IPredicate>>();
	}

	public Map<IPredicate, Set<IPredicate>> getLocationsToSetOfPredicates() {
		return m_LocationsToSetOfPredicates;
	}
	
	/**
	 * Remove the predicates from the set of the consolidated predicates which only lead to a final state in the difference automaton. 
	 * @param badPredicates - a set of states from the difference automaton
	 */
	public void removeBadPredicates(Set<IPredicate> badPredicates) {
		for (IPredicate p : badPredicates) {
			AbstractMap.SimpleEntry<IPredicate, IPredicate> argumentPredicates = m_IntersectedPredicateToArgumentPredicates.get(p);
			Set<IPredicate> consolidatePredicates = m_LocationsToSetOfPredicates.get(argumentPredicates.getKey());
			consolidatePredicates.remove(argumentPredicates.getValue());
		}
	}
	
	@Override
	public IPredicate intersection(IPredicate p1, IPredicate p2) {
		// 1. Do the intersection
		assert (p1 instanceof ISLPredicate);
		
		ProgramPoint pp = ((ISLPredicate) p1).getProgramPoint();
		
		TermVarsProc tvp = super.m_SmtManager.and(p1, p2);
		IPredicate result = super.m_SmtManager.newSPredicate(pp, tvp);
		
		if (m_IntersectedPredicateToArgumentPredicates.containsKey(result)) {
			throw new AssertionError("States of difference automaton are not unique!");
		}
		AbstractMap.SimpleEntry<IPredicate, IPredicate> predicateArguments = new AbstractMap.SimpleEntry<IPredicate, IPredicate>(p1, p2);
		m_IntersectedPredicateToArgumentPredicates.put(result, predicateArguments);
		
		
		// 2. Store the predicates in the map
		if (m_LocationsToSetOfPredicates.containsKey(p1)) {
			Set<IPredicate> predicates = m_LocationsToSetOfPredicates.get(p1);
			predicates.add(p2);
		} else {
			Set<IPredicate> predicatesForThisLocation = new HashSet<IPredicate>();
			predicatesForThisLocation.add(p2);
			m_LocationsToSetOfPredicates.put(p1, predicatesForThisLocation);
		}
		return result;
	}
}
