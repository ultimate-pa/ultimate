package de.uni_freiburg.informatik.ultimatetest.svcomp;

import java.util.HashMap;
import java.util.Map;

import org.junit.Ignore;

import de.uni_freiburg.informatik.ultimatetest.Util;

@Ignore
public class CodeCheckTestSuite extends AbstractSVCOMP14TestSuite {

	@Override
	protected String getToolchainPath() {
		return Util.getPathFromTrunk("examples/toolchains/KojakC.xml");
	}

	@Override
	protected long getDeadline() {
		return 30000;
	}

	@Override
	protected Map<String, String> getCategoryToSettingsPathMap() {
		HashMap<String, String> map = new HashMap<String, String>();
		map.put("ControlFlowInteger", Util.getPathFromTrunk("examples/settings/AlexSVCOMPmemsafety"));
		return map;
	}

	@Override
	protected boolean getCreateLogfileForEachTestCase() {
		return true;
	}

	@Override
	protected String getSVCOMP14RootDirectory() {
		return Util.getPathFromTrunk("../../svcomp");
	}
}
