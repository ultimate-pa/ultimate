package de.uni_freiburg.informatik.ultimatetest.svcomp;

import java.io.File;

import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider_OldVersion;
import de.uni_freiburg.informatik.ultimatetest.util.Util.ExpectedResult;

public class SVCOMP14TestResultDecider extends SafetyCheckTestResultDecider_OldVersion {

	public SVCOMP14TestResultDecider(File inputFile) {
		super(inputFile);
	}

	@Override
	protected void generateExpectedResult(File inputFile) {
		// SVCOMP has different rules for which file is "safe" and which not
		boolean shouldbesafe = inputFile.getName().contains("true");
		if (!shouldbesafe) {
			if (!inputFile.getName().contains("false")) {
				throw new RuntimeException("Should contain false");
			}
		}
		if (shouldbesafe) {
			setExpectedResult(ExpectedResult.SAFE);
		} else {
			setExpectedResult(ExpectedResult.UNSAFE);
		}
	}

}
