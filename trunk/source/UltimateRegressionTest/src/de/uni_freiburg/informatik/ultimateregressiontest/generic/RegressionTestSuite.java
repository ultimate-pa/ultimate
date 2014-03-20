package de.uni_freiburg.informatik.ultimateregressiontest.generic;

import java.io.File;

import de.uni_freiburg.informatik.ultimateregressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.util.Util;


/**
 * 
 * @author dietsch
 *
 */
public class RegressionTestSuite extends AbstractRegressionTestSuite {

	public RegressionTestSuite(){
		super();
		mTimeout = 5000;
		mRootFolder = Util.getPathFromTrunk("examples/");
		
		//match every path not containing CToBoogieTranslation
		mFilterRegex = "((?!CToBoogieTranslation)[\\s\\S])*";
	}
	
	@Override
	protected ITestResultDecider getTestResultDecider(File inputFile) {
		return new RegressionTestResultDecider(inputFile);
	}
}
