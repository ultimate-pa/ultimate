/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.io.File;
import java.util.Collection;

import org.junit.Ignore;

import de.uni_freiburg.informatik.ultimatetest.Util;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */

public class ExamplesInMinitestsDirectoryTraceAbstractionTestSuite extends
		AbstractTraceAbstractionTestSuite {
	private static final String m_PathToMiniTestDir = "examples/programs/minitests/";
	
	
	
	public ExamplesInMinitestsDirectoryTraceAbstractionTestSuite() {
		m_TestBoogieFiles = true;
		m_TestCFiles = false;
		m_useForwardPredicates = false;
		m_useBackwardPredicates = true;
		m_Timeout = 10;
	}



	@Override
	protected Collection<File> getInputFiles(String[] fileEndings) {
		return Util.getFiles(new File(Util.getPathFromTrunk(m_PathToMiniTestDir)),
				fileEndings);
	}

	
}
