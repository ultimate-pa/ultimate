package de.uni_freiburg.informatik.ultimatetest.translation;

import java.io.File;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

public class SVCOMPCTranslationTestSuite extends AbstractCTranslationTestSuite {

//	private static File sInputDirectory = new File(Util.getFromMavenVariableSVCOMPRoot("../../svcomp/"));
//	private static File sInputDirectory = new File(TestUtil.getPathFromTrunk("examples/svcomp/ldv-regression"));
	private static File sInputDirectory = new File(TestUtil.getPathFromTrunk("examples/svcomp/ldv-linux-3.0"));
	private static File sSettings = new File(TestUtil.getPathFromTrunk("examples/settings/automizer/ForwardPredicates_SvcompReachPreciseMM.epf"));
	

	@Override
	public Collection<File> getInputFiles() {
		return TestUtil.getFiles(sInputDirectory, new String[] { ".c", ".i" });
	}
	
	@Override 
	public File getSettings() {
		return sSettings;
	}

}
