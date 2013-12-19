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
@Ignore
public class Examples_MinitestsDirectoryBPLTraceAbstractionTestSuite extends
		AbstractTraceAbstractionTestSuite {


	@Override
	public Collection<File> getInputFiles() {
		return Util.getFiles(new File(Util.getPathFromTrunk("examples/programs/minitests/")),
				new String[] { ".bpl"});
	}

}
