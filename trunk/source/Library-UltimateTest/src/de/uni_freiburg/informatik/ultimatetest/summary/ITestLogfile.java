package de.uni_freiburg.informatik.ultimatetest.summary;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;

/**
 * Provides methods from which UltimateTest deduces filenames of logs or summaries. 
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public interface ITestLogfile {

	/**
	 * Class of the UltimateTestSuite for which this log file will be written.
	 * Some aspects of the class are part of the filename.
	 */
	public Class<? extends UltimateTestSuite> getUltimateTestSuiteClass();

	/**
	 * Description of this type of logfile, e.g., "AutomataScriptSummary",
	 * "TraceAbstractionBenchmarks". This String is part of the filename to
	 * which this summary is written.
	 * 
	 */
	public String getDescriptiveLogName();

	/**
	 * Filename extension of the log file that will be written. E.g., ".log", or
	 * ".csv"
	 */
	public String getFilenameExtension();

}