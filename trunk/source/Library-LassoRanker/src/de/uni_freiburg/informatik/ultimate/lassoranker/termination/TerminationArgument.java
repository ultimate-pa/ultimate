/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lassoranker.termination;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.logic.Term;


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
	
	private final RankingFunction mranking_function;
	private final Collection<SupportingInvariant> msupporting_invariants;
	
	/**
	 * Set of supporting invariants that were discovered during preprocessing.
	 */
	private final Set<Term> mArrayIndexSupportingInvariants;
	
	/**
	 * Construct a termination argument
	 * @param ranking_function a ranking function
	 * @param supporting_invariants a collection of required supporting
	 *                              invariants
	 * @param arrayIndexSupportingInvariants 
	 */
	public TerminationArgument(RankingFunction ranking_function,
			Collection<SupportingInvariant> supporting_invariants, 
			Set<Term> arrayIndexSupportingInvariants) {
		assert(ranking_function != null);
		mranking_function = ranking_function;
		assert(supporting_invariants != null);
		
		// Add only non-trivial supporting invariants
		msupporting_invariants = new ArrayList<SupportingInvariant>();
		for (final SupportingInvariant si : supporting_invariants) {
			if (!si.isTrue()) {
				msupporting_invariants.add(si);
			}
		}
		mArrayIndexSupportingInvariants = arrayIndexSupportingInvariants;
	}
	
	/**
	 * @return the ranking function
	 */
	public RankingFunction getRankingFunction() {
		return mranking_function;
	}
	
	/**
	 * @return the supporting invariants
	 */
	public Collection<SupportingInvariant> getSupportingInvariants() {
		return Collections.unmodifiableCollection(msupporting_invariants);
	}
	
	public Collection<Term> getArrayIndexSupportingInvariants() {
		return Collections.unmodifiableCollection(
											mArrayIndexSupportingInvariants);
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Termination argument consisting of:\n");
		sb.append("Ranking function ");
		sb.append(mranking_function);
		sb.append("\n");
		sb.append("Supporting invariants ");
		sb.append(msupporting_invariants);
		return sb.toString();
	}
}
