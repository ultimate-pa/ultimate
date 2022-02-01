/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE UnitTest Library.
 * 
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE UnitTest Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.decider.expectedresult;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;

/**
 * Classes that implement this interface are used to find out the expected
 * result of an ultimate run.
 * Such an evaluation does not use IResults of ultimate. The expected result
 * is typically obtained from keywords in the filename, comments in the file
 * or via a lookup in a user provided database or separate file.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <OVERALL_RESULT> Type that we use to represent possible overall
 * results. Typically we use an enum type.
 */
public interface IExpectedResultFinder<OVERALL_RESULT> {
	
	/**
	 * Specifies if we were able to find an expected result.
	 */
	public enum ExpectedResultFinderStatus {
		/**
		 * No expected result was found. E.g. filenames does not have any
		 * comment, file not part of database with user defined results.
		 */
		NO_EXPECTED_RESULT_FOUND,
		/**
		 * Evaluation was successful.
		 */
		EXPECTED_RESULT_FOUND,
		/**
		 * Unable to determine an expected result. E.g., because of 
		 * contradiction between keywords in filename and result database.
		 */
		ERROR
	}

	/**
	 * Try to find an expected result and make outcome of search available
	 * via getters. 
	 */
	public void findExpectedResult(UltimateRunDefinition ultimateRunDefinition);
	
	/**
	 * Returns if we were able to find and expected result. This method does
	 * not return the expected result itself.
	 */
	public ExpectedResultFinderStatus getExpectedResultFinderStatus();

	/**
	 * Describes the success of our search for an expected result.
	 */
	public String getExpectedResultFinderMessage();
	
	/**
	 * Returns an OVERALL_RESULT if outcome of search is EXPECTED_RESULT_FOUND,
	 * otherwise null is returned.
	 */
	public OVERALL_RESULT getExpectedResult();
}
