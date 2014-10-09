package de.uni_freiburg.informatik.ultimatetest.summary;

import de.uni_freiburg.informatik.ultimate.util.Utils;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class IncrementalLogWithVMParameters extends DefaultIncrementalLogfile {

	private boolean mFirstRun;

	public IncrementalLogWithVMParameters(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
		mFirstRun = true;
	}

	@Override
	public void addEntryPreStart(UltimateRunDefinition urd) {
		StringBuilder sb = new StringBuilder();

		if (mFirstRun) {
			sb.append(Util.getCurrentDateTimeAsString());
			sb.append(" First run of ");
			sb.append(getDescriptiveLogName());
			sb.append(Util.getPlatformLineSeparator());
			// add more stats here
			sb.append("\t")
					.append(String.format("Parameters: heapMaxSize=%s",
							Utils.humanReadableByteCount(Runtime.getRuntime().maxMemory(), true)))
					.append(Util.getPlatformLineSeparator());
			mFirstRun = false;
		}

		sb.append(Util.getCurrentDateTimeAsString());
		sb.append(" ### Starting test for ");
		sb.append(urd);
		sb.append(Util.getPlatformLineSeparator());
		writeToFile(sb.toString());
	}

}
