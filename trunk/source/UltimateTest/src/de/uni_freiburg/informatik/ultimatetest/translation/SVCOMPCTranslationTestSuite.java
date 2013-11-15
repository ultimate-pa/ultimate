package de.uni_freiburg.informatik.ultimatetest.translation;

import java.io.File;
import java.util.Collection;

import org.junit.Ignore;

import de.uni_freiburg.informatik.ultimatetest.Util;

@Ignore
public class SVCOMPCTranslationTestSuite extends AbstractCTranslationTestSuite {

	@Override
	public Collection<File> getInputFiles() {
		return Util.getFiles(
				new File(Util.getFromMavenVariableSVCOMPRoot("../../svcomp/")),
				new String[] { ".c", ".i" });
	}

}
