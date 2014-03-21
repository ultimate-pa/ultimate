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

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;


/**
 * A RankVar is a variable that is relevant to ranking functions or
 * supporting invariants. It is either a BoogieVar or an auxiliary variable
 * created in the preprocessing steps.
 * 
 * @author Jan Leike
 * 
 * @see BoogieVarWrapper
 * @see AuxVar
 */
public abstract class RankVar implements Serializable {
	private static final long serialVersionUID = -3215866247258690258L;
	
	/**
	 * @return the term that this auxiliary variable is replacing
	 */
	public abstract Term getDefinition();
	
	/**
	 * @return a globally unique identifier for this variable
	 */
	public abstract String getGloballyUniqueId();
	
	/**
	 * @return the associated BoogieVar and null if there is no such association
	 */
	public abstract BoogieVar getAssociatedBoogieVar();
}
