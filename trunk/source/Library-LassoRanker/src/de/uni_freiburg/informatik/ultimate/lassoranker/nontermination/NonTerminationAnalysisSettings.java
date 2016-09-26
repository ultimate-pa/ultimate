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
package de.uni_freiburg.informatik.ultimate.lassoranker.nontermination;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;


/**
 * Various (local) settings for nontermination analysis
 * 
 * A new NonTerminationAnalysisSettings object can be used for each
 * nontermination analysis
 * 
 * This class functions much like a struct and is implemented like one.
 * 
 * @author Jan Leike
 */
public class NonTerminationAnalysisSettings implements Serializable {
	private static final long serialVersionUID = 4249624228131593458L;

	/**
	 * What analysis type should be used for the nontermination analysis?
	 * Use a linear SMT query, use a linear SMT query but guess some eigenvalues
	 * of the loop, or use a nonlinear SMT query?
	 */
	public AnalysisType analysis = AnalysisType.LINEAR_WITH_GUESSES;
		// Default: AnalysisType.LINEAR_PLUS_GUESSES
	
	/**
	 * Allow finding nontermination arguments that are bounded executions?
	 */
	public boolean allowBounded = true;
	
	/**
	 * Number of generalized eigenvectors in the geometric nontermination argument
	 */
	public int number_of_gevs = 3;
	
	/**
	 * Allow nilpotent components in the geometric nontermination argument?
	 */
	public boolean nilpotent_components = true;
	
	/*
	 * As this point there is not much here, but there might be in the future.
	 */
	
	/**
	 * Default construction initializes default values
	 */
	public NonTerminationAnalysisSettings() {
	}
	
	/**
	 * Copy constructor copies everything
	 */
	public NonTerminationAnalysisSettings(NonTerminationAnalysisSettings other) {
		analysis = other.analysis;
		allowBounded = other.allowBounded;
		number_of_gevs = other.number_of_gevs;
		nilpotent_components = other.nilpotent_components;
	}
	
	/**
	 * Verify that the settings are self-consistent and sane.
	 * Only makes assertion calls.
	 */
	public void checkSanity() {
		assert number_of_gevs >= 0;
	}
	
	/**
	 * Build a string description of the current preferences
	 */
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Nontermination analysis: ");
		sb.append(analysis);
		sb.append("\nAllow bounded executions: ");
		sb.append(allowBounded);
		sb.append("\nNumber of generalized eigenvectors: ");
		sb.append(number_of_gevs);
		sb.append("\nNilpotent components: ");
		sb.append(nilpotent_components);
		return sb.toString();
	}
}
