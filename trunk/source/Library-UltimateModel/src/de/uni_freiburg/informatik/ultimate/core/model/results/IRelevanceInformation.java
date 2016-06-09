/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.model.results;

/**
 * Objects that implement this interface provide information whether a trace
 * element in a counterexample trace is relevant for reaching the error.
 * E.g., we could say that in the error trace
 *     x:=0; y++; assume x==0;
 * the statement y++ is irrelevant because the error is still reachable
 * if we replace it y++ by a skip statement.
 * 
 * An IRelevanceInformation object may provide relevance information with 
 * respect to several relevance criteria.
 *  
 *   
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public interface IRelevanceInformation {
	
	/**
	 * Merge several {@link IRelevanceInformation}s into one.
	 * This is needed in our backtranslation. Sometimes we represent a 
	 * statement in a high-level language by several statements in a low-level
	 * language. While translating a counterexample from the low-level language
	 * back to the high-level language we have to merge the 
	 * {@link IRelevanceInformation}s of all low-level language statements
	 * into a new {@link IRelevanceInformation} for the high-level statement.
	 * If one low-level statement is relevant according to 
	 * relevance criterion A and another low-level statement is relevant 
	 * according relevance criterion B the high-level statement is relevant
	 * according to relevance citerion A And relevance criterion B.
	 * 
	 * @return A new {@link IRelevanceInformation} that represents the 
	 * relevance of all input {@link IRelevanceInformation}s.
	 */
	public IRelevanceInformation merge(IRelevanceInformation... relevanceInformations);


	/**
	 * Very brief representation of the relevance of a trace element.
	 * That will be shown in the counterexample result.
	 * This representation could be e.g., up to three stars.
	 */
	public String getShortString();
}
