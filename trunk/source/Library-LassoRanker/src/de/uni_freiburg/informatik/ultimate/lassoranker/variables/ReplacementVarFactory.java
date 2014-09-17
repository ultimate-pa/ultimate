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

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Factory for constructing ReplacementVars ensures that for each defining
 * Term exactly one ReplacementVar is constructed.
 * @author Matthias Heizmann
 *
 */
public class ReplacementVarFactory {
	private final Map<Term, ReplacementVar> m_Mapping = 
			new HashMap<Term, ReplacementVar>();
	
	/**
	 * Get the ReplacementVar that is used as a replacement for the Term
	 * definition. Construct this ReplacementVar if it does not exist yet.
	 */
	public ReplacementVar getOrConstuctReplacementVar(Term definition) {
		ReplacementVar repVar = m_Mapping.get(definition);
		if (repVar == null) {
			repVar = new ReplacementVar(definition.toString(), definition);
			m_Mapping.put(definition, repVar);
		}
		return repVar;
	}

}
