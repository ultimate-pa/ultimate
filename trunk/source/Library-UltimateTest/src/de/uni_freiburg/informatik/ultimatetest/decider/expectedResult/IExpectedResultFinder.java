package de.uni_freiburg.informatik.ultimatetest.decider.expectedResult;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;

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