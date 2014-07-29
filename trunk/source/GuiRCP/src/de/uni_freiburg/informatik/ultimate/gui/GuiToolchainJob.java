package de.uni_freiburg.informatik.ultimate.gui;

import java.io.File;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
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

	@Override
	protected void releaseToolchain(IToolchain currentToolchain) {
		((GuiController) mController).setCurrentToolchain(currentToolchain);
	}

}
