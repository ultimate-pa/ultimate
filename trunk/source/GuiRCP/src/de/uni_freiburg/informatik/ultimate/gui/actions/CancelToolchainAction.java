/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.gui.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;
import org.eclipse.ui.plugin.AbstractUIPlugin;

import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IImageKeys;

/**
 *
 * Cancel the toolchain with the press of a button.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CancelToolchainAction extends Action implements IWorkbenchAction {

	private final IWorkbenchWindow mWindow;
	private final ILogger mLogger;
	private final GuiController mGuiController;

	public CancelToolchainAction(final IWorkbenchWindow window, final GuiController controller, final ILogger logger) {
		setId(getClass().getName());
		setText("Cancel Toolchain");
		setToolTipText("Cancel the currently running toolchain");
		setImageDescriptor(
				AbstractUIPlugin.imageDescriptorFromPlugin(GuiController.PLUGIN_ID, IImageKeys.ICON_CANCEL_TOOLCHAIN));
		mLogger = logger;
		mGuiController = controller;
		mWindow = window;
	}

	@Override
	public void run() {
		final IToolchain<RunDefinition> currentTc = mGuiController.getCurrentToolchain();
		if (currentTc == null) {
			mLogger.warn("There is no toolchain running");
			return;
		}
		final IToolchainData<RunDefinition> tcData = currentTc.getCurrentToolchainData();
		if (tcData == null) {
			mLogger.warn("Current toolchain has no data");
			return;
		}
		final IUltimateServiceProvider services = tcData.getServices();
		if (services == null) {
			mLogger.warn("Current toolchain has no services");
			return;
		}
		final IProgressMonitorService progressService = services.getProgressMonitorService();
		if (progressService == null) {
			// there is not toolchain running
			return;
		}
		progressService.cancelToolchain();
		mLogger.info("User requested toolchain termination....");
	}

	@Override
	public void dispose() {
		// do nothing
	}

}
