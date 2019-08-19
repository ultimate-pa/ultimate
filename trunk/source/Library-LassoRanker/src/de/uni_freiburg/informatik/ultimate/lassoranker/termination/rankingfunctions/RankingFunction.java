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
package de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions;

import java.io.Serializable;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;


/**
 * A ranking function is a function that proves termination for a given program.
 * 
 * @author Jan Leike
 */
public abstract class RankingFunction implements Serializable {
	private static final long serialVersionUID = 4774387985755366720L;
	
	/**
	 * @return Name of this ranking function (e.g., affine, 2-phase, 3-nesting)
	 */
	public abstract String getName();
	
	/**
	 * @return the set of all variables occurring in the ranking function
	 */
	public abstract Set<IProgramVar> getVariables();
	
	/**
	 * @return the ranking function's codomain
	 */
	public abstract Ordinal codomain();
	
	/**
	 * Evaluate the ranking function
	 * @param assignment the variable assignment
	 * @return value of the function as an ordinal
	 */
	public abstract Ordinal evaluate(Map<IProgramVar, Rational> assignment);
	
	/**
	 * Return the ranking function as a lexicographically ordered list of
	 * SMTLib terms, with the highest component being the list's first item.
	 * The length of this list is asserted to be constant throughout the
	 * lifetime of this object.
	 * 
	 * @param script the current script
	 */
	public abstract Term[] asLexTerm(Script script) throws SMTLIBException;
}
