package de.uni_freiburg.informatik.ultimatetest.svcomp;

import java.util.HashMap;
import java.util.Map;

import org.junit.Ignore;

import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

@Ignore
public class CodeCheckTestSuite extends AbstractSVCOMP14TestSuite {

	@Override
	protected String getToolchainPath() {
		return TestUtil.getPathFromTrunk("examples/toolchains/KojakC.xml");
	}

	@Override
	protected long getDeadline() {
		return 30000;
	}

	@Override
	protected Map<String, String> getCategoryToSettingsPathMap() {
		HashMap<String, String> map = new HashMap<String, String>();
		map.put("ControlFlowInteger", TestUtil.getPathFromTrunk("examples/settings/AlexSVCOMPmemsafety"));
		return map;
	}

	@Override
	protected boolean getCreateLogfileForEachTestCase() {
		return true;
	}

	@Override
	protected String getSVCOMP14RootDirectory() {
		return TestUtil.getPathFromTrunk("../../svcomp");
	}
}
