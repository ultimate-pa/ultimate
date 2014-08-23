package de.uni_freiburg.informatik.ultimatetest.translation;

import java.io.File;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summary.TestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class TranslationTestSummary extends TestSummary {

	public TranslationTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
	}
	
	@Override
	public String getSummaryTypeDescription() {
		return this.getClass().getSimpleName();
	}
	
	@Override
	public String getFilenameExtension() {
		return ".log";
	}

	@Override
	public String getSummaryLog() {
		return generateCanonicalSummary().toString();
	}

}
