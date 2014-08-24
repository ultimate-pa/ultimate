package de.uni_freiburg.informatik.ultimatetest.translation;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.junit.Ignore;

import de.uni_freiburg.informatik.ultimatetest.automatascript.AutomataScriptTestSummary;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

@Ignore
public class SVCOMPCTranslationTestSuite extends AbstractCTranslationTestSuite {

	private static File sInputDirectory = new File(Util.getFromMavenVariableSVCOMPRoot("../../svcomp/"));
	
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
