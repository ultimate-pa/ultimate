package de.uni_freiburg.informatik.ultimatetest.translation;

import java.io.File;
import java.util.Collection;

import org.junit.Ignore;

import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class SVCOMPCTranslationTestSuite extends AbstractCTranslationTestSuite {

//	private static File sInputDirectory = new File(Util.getFromMavenVariableSVCOMPRoot("../../svcomp/"));
	private static File sInputDirectory = new File(Util.getPathFromTrunk("examples/svcomp/ldv-regression"));
	
	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] {
				new TranslationTestSummary(this.getClass())
		};
	}

	@Override
	public Collection<File> getInputFiles() {
		return Util.getFiles(sInputDirectory, new String[] { ".c", ".i" });
	}

}
