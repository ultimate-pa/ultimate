/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE DebugGUI plug-in.
 *
 * The ULTIMATE DebugGUI plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE DebugGUI plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE DebugGUI plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE DebugGUI plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE DebugGUI plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.gui;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class GuiToolchainJob extends DefaultToolchainJob {

	public GuiToolchainJob(final String name, final ICore<RunDefinition> core, final GuiController controller,
			final File[] inputFiles, final ILogger logger) {
		super(name, core, controller, logger, inputFiles);
	}

	public GuiToolchainJob(final String name, final ICore<RunDefinition> core,
			final IController<RunDefinition> controller, final ILogger logger,
			final IToolchain<RunDefinition> toolchain) {
		super(name, core, controller, logger, toolchain);
	}

	public GuiToolchainJob(final String name, final ICore<RunDefinition> core,
			final IController<RunDefinition> controller, final ILogger logger, final IToolchainData<RunDefinition> data,
			final File[] inputFiles) {
		super(name, core, controller, logger, data, inputFiles);
	}

	@Override
	protected void releaseToolchain() {
		// save the current toolchain to the controller instead of releasing it
		// directly; the controller will save one toolchain and release the last
		// if it is overwritten

		// if the current toolchain has no toolchain data, it is broken and should be released immediately
		if (mToolchain.getCurrentToolchainData() == null) {
			super.releaseToolchain();
		} else {
			((GuiController) mController).setAfterRerunCurrentToolchain(mToolchain);
		}
	}
}
