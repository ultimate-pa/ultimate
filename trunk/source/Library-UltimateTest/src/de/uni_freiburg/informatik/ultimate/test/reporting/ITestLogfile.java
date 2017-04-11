/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE UnitTest Library.
 * 
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.reporting;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;

/**
 * Provides methods from which UltimateTest deduces filenames of logs or summaries.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public interface ITestLogfile {

	/**
	 * Class of the UltimateTestSuite for which this log file will be written. Some aspects of the class are part of the
	 * filename.
	 */
	Class<? extends UltimateTestSuite> getUltimateTestSuiteClass();

	/**
	 * Description of this type of logfile, e.g., "AutomataScriptSummary", "TraceAbstractionBenchmarks". This String is
	 * part of the filename to which this summary is written.
	 * 
	 */
	String getDescriptiveLogName();

	/**
	 * Filename extension of the log file that will be written. E.g., ".log", or ".csv"
	 */
	String getFilenameExtension();

}
