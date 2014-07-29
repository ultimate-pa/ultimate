package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.services.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;

public class TestToolchainJob extends DefaultToolchainJob {

	public TestToolchainJob(String name, ICore core, IController controller, Logger logger, File input,
			PreludeProvider preludefile) {
		super(name, core, controller, logger, input, preludefile);
	}

	@Override
	protected void releaseToolchain() {
		// we use a manual release
	}

	public void releaseToolchainManually() {
		super.releaseToolchain();
	}

}
