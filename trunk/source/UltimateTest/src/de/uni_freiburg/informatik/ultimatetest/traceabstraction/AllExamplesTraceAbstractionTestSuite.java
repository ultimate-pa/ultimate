/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.io.File;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.Util;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class AllExamplesTraceAbstractionTestSuite extends
		AbstractTraceAbstractionTestSuite {
	
	private static final String m_PathToAllExamples = "examples/programs/";

	
	
	public AllExamplesTraceAbstractionTestSuite() {
		m_TestBoogieFiles = true;
		m_TestCFiles = false;
		m_useForwardPredicates = false;
		m_useBackwardPredicates = true;
		m_Timeout = 20;
	}

	@Override
	protected Collection<File> getInputFiles(String[] fileEndings) {
		return Util.getFiles(new File(Util.getPathFromTrunk(m_PathToAllExamples)),
				fileEndings);
	}

}
