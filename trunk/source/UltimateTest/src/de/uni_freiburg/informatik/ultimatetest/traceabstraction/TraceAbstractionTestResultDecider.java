package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.io.File;

import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider_OldVersion;

public class TraceAbstractionTestResultDecider extends SafetyCheckTestResultDecider_OldVersion {

	private File mSettingsFile;

	public TraceAbstractionTestResultDecider(File inputFile,File settingsFile) {
		super(inputFile);
		mSettingsFile = settingsFile;
	}

	@Override
	public boolean getJUnitTestResult(TestResult actualResult) {
		// Matthias wants to see Unknown results as success
		switch (actualResult) {
		case FAIL:
			return false;
		case SUCCESS:
		case UNKNOWN:
			return true;
		default:
			throw new IllegalArgumentException("actualResult has an unknown value");
		}
	}

	public File getSettingsFile() {
		return mSettingsFile;
	}
}
