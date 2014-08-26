package de.uni_freiburg.informatik.ultimate.gui;

import java.io.File;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.services.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchain;

public class GuiToolchainJob extends DefaultToolchainJob {

	public GuiToolchainJob(String name, ICore core, GuiController controller, File boogieFiles,
			PreludeProvider preludefile, Logger logger) {
		super(name, core, controller, logger, boogieFiles, preludefile);
	}

	public GuiToolchainJob(String name, ICore core, IController controller, Logger logger, IToolchain toolchain) {
		super(name, core, controller, logger, toolchain);
	}

	public GuiToolchainJob(String name, ICore core, IController controller, Logger logger, ToolchainData data,
			File inputfile, PreludeProvider prelude) {
		super(name, core, controller, logger, data, inputfile, prelude);
	}

	@Override
	protected void releaseToolchain() {
		// save the current toolchain to the controller instead of releasing it
		// directly; the controller will save one toolchain and release the last
		// if it is overwritten
		
		//if the current toolchain has no toolchain data, it is broken and should be released immediatly 
		if (mToolchain.getCurrentToolchainData() == null) {
			super.releaseToolchain();
		} else {
			((GuiController) mController).setCurrentToolchain(mToolchain);
		}
	}

}
