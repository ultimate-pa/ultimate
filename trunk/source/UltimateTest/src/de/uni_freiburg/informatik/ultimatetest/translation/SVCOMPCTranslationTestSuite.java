package de.uni_freiburg.informatik.ultimatetest.translation;

import java.io.File;
import java.util.Collection;

import org.junit.Ignore;

import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

@Ignore
public class SVCOMPCTranslationTestSuite extends AbstractCTranslationTestSuite {

	private static File sInputDirectory = new File(Util.getFromMavenVariableSVCOMPRoot("../../svcomp/"));

	@Override
	public Collection<File> getInputFiles() {
		return Util.getFiles(sInputDirectory, new String[] { ".c", ".i" });
	}

	@Override
	public ITestSummary getSummary() {
		return new TranslationTestSummary(this.getClass());
	}

}
