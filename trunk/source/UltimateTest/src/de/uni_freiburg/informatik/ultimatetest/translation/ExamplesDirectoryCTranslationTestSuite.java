package de.uni_freiburg.informatik.ultimatetest.translation;

import java.io.File;
import java.util.Collection;

import org.junit.Ignore;

import de.uni_freiburg.informatik.ultimatetest.Util;

@Ignore
public class ExamplesDirectoryCTranslationTestSuite extends
		AbstractCTranslationTestSuite {

	@Override
	public Collection<File> getInputFiles() {
		return Util.getFiles(new File(Util.getPathFromTrunk("examples/")),
				new String[] { ".c", ".i" });
	}

}
