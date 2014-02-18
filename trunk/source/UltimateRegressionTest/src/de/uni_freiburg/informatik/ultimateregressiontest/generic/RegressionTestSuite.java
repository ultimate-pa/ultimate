package de.uni_freiburg.informatik.ultimateregressiontest.generic;

import java.io.File;

import org.junit.Ignore;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimateregressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimatetest.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.Util;


@Ignore
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
	
	@Test
	public void SomeFakeTest(){
		
	}

}
