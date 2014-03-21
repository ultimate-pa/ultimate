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

import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;


/**
 * Represents a termination argument for a lasso program.
 * 
 * The termination argument consists of
 * <ul>
 * <li> a ranking function, and
 * <li> a set of supporting invariants that are required to prove the ranking
 *      function.
 * </ul>
 * 
 * @author Jan Leike
 */
public class TerminationArgument implements Serializable {
	private static final long serialVersionUID = 3480670605705583627L;
	
	private final RankingFunction m_ranking_function;
	private final Collection<SupportingInvariant> m_supporting_invariants;
	
	/**
	 * Construct a termination argument
	 * @param ranking_function a ranking function
	 * @param supporting_invariants a collection of required supporting
	 *                              invariants
	 */
	public TerminationArgument(RankingFunction ranking_function,
			Collection<SupportingInvariant> supporting_invariants) {
		assert(ranking_function != null);
		m_ranking_function = ranking_function;
		assert(supporting_invariants != null);
		
		// Add only non-trivial supporting invariants
		m_supporting_invariants = new ArrayList<SupportingInvariant>();
		for (SupportingInvariant si : supporting_invariants) {
			if (!si.isTrue()) {
				m_supporting_invariants.add(si);
			}
		}
		
	}
	
	/**
	 * @return the ranking function
	 */
	public RankingFunction getRankingFunction() {
		return m_ranking_function;
	}
	
	/**
	 * @return the supporting invariants
	 */
	public Collection<SupportingInvariant> getSupportingInvariants() {
		return Collections.unmodifiableCollection(m_supporting_invariants);
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Termination argument consisting of:\n");
		sb.append("Ranking function ");
		sb.append(m_ranking_function);
		sb.append("\n");
		sb.append("Supporting invariants ");
		sb.append(m_supporting_invariants);
		return sb.toString();
	}
}
