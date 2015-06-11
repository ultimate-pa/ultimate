package de.uni_freiburg.informatik.ultimatetest.suites.translation;

import java.io.File;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

public class ExamplesDirectoryCTranslationTestSuite extends AbstractCTranslationTestSuite {

	private static File sInputDirectory = new File(TestUtil.getPathFromTrunk("examples/"));
	
	@Override
	public Collection<File> getInputFiles() {
		return TestUtil.getFiles(sInputDirectory, new String[] { ".c", ".i" });
	}

}
