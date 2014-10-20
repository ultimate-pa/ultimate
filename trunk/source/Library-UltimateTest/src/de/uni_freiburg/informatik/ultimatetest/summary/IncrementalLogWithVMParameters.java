package de.uni_freiburg.informatik.ultimatetest.summary;

import de.uni_freiburg.informatik.ultimate.util.Utils;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class IncrementalLogWithVMParameters extends DefaultIncrementalLogfile {

	private boolean mFirstRun;
	private int mCountTotal;
	private int mCountCurrent;
	private long mDeadline;

	public IncrementalLogWithVMParameters(Class<? extends UltimateTestSuite> ultimateTestSuite, long deadline) {
		super(ultimateTestSuite);
		mFirstRun = true;
		mCountCurrent = 0;
		mCountTotal = 0;
		mDeadline = deadline;
	}

	public void setCountTotal(int total) {
		mCountTotal = total;
	}

	@Override
	public void addEntryPreStart(UltimateRunDefinition urd) {
		mCountCurrent++;
		StringBuilder sb = new StringBuilder();
		String indent = "\t";
		if (mFirstRun) {
			sb.append(Util.getCurrentDateTimeAsString());
			sb.append(" First run of ");
			sb.append(getDescriptiveLogName());
			sb.append(Util.getPlatformLineSeparator());
			// add more stats here
			sb.append(indent)
					.append(String.format("Parameters: heapMaxSize=%s",
							Utils.humanReadableByteCount(Runtime.getRuntime().maxMemory(), true)))
					.append(Util.getPlatformLineSeparator());
			sb.append(indent).append(String.format("Test Suite Parameters: Timeout=%s s", mDeadline / 1000))
					.append(Util.getPlatformLineSeparator());

			mFirstRun = false;
		}
		sb.append(Util.getCurrentDateTimeAsString());
		sb.append(" ### ");
		sb.append(mCountCurrent);
		if (mCountTotal != 0) {
			sb.append("/");
			sb.append(mCountTotal);
		}
		sb.append(" ### Starting test for ");
		sb.append(urd);
		sb.append(Util.getPlatformLineSeparator());
		writeToFile(sb.toString());
	}

}
