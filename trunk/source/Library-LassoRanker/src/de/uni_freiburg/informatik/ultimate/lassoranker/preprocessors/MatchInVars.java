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
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableManager;


/**
 * Add a corresponding inVar for all outVars.
 * 
 * This is required to prevent a problem that was reported by Matthias
 * in Madrid.bpl. This problem occurs when there are outVars that do not
 * have a corresponding inVar. Supporting invariant generation then becomes
 * unsound for the inductiveness property.
 */
public class MatchInVars extends TransitionPreProcessor {

	/**
	 * Factory for construction of auxVars.
	 */
	private final VariableManager m_VariableManager;
	
	public MatchInVars(VariableManager variableManager) {
		super();
		m_VariableManager = variableManager;
	}

	@Override
	public String getDescription() {
		return "Add a corresponding inVar for all outVars";
	}
	
	@Override
	protected TransFormulaLR process(Script script, TransFormulaLR tf) throws TermException {
		for (Map.Entry<RankVar, Term> entry : tf.getOutVars().entrySet()) {
			if (!tf.getInVars().containsKey(entry.getKey())) {
				TermVariable inVar = m_VariableManager.constructFreshTermVariable(
						entry.getKey().getGloballyUniqueId(),
						entry.getValue().getSort()
				);
				tf.addInVar(entry.getKey(), inVar);
			}
		}
		return tf;
	}
}
