package de.uni_freiburg.informatik.ultimateregressiontest.generic;

import java.io.File;

import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider_OldVersion;

/**
 * This {@link ITestResultDecider} tries to interpret the results of Ultimate's
 * model checking tools to allow easy generation of regression tests.
 * 
 * @author dietsch
 * 
 */
public class RegressionTestResultDecider extends SafetyCheckTestResultDecider_OldVersion {

	public RegressionTestResultDecider(File inputFile) {
		super(inputFile);
	}
	
	@Override
	protected void generateResultMessageAndCategory(SafetyCheckerResult safetycheckerresult) {
		// we override this method so that no summary informations are generated 
	}
	
	
}
