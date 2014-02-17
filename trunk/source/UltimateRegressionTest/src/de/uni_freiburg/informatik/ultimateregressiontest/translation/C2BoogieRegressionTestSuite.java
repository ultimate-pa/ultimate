package de.uni_freiburg.informatik.ultimateregressiontest.translation;

import java.io.File;


import de.uni_freiburg.informatik.ultimateregressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimatetest.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.Util;


public class C2BoogieRegressionTestSuite extends
		AbstractRegressionTestSuite {

	public C2BoogieRegressionTestSuite(){
		super();
		mTimeout = 5000;
		mRootFolder = Util.getPathFromTrunk("examples/CToBoogieTranslation");
	}
	
	@Override
	protected ITestResultDecider getTestResultDecider(File inputFile) {
		return new TranslationTestResultDecider(inputFile.getAbsolutePath());
	}


}
