/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 Jürgen Christ (christj@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.gui.actions;

import java.io.File;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.GuiRerunFreshToolchainJob;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IImageKeys;

/**
 * Execute old toolchain on new file(s)
 *
 * @author dietsch
 */

public class ResetAndRedoToolChainOldTCAction extends RunToolchainAction implements IWorkbenchAction {

	private static final String LABEL = "Execute current Toolchain on new file(s)";

	public ResetAndRedoToolChainOldTCAction(final IWorkbenchWindow window, final ICore<RunDefinition> icore,
			final GuiController controller, final ILogger logger) {
		super(logger, window, icore, controller, ResetAndRedoToolChainOldTCAction.class.getName(), LABEL,
				IImageKeys.REEXECOLDTC);
	}

	/**
	 * ! This is a generated comment ! The action has been activated. The argument of the method represents the 'real'
	 * action sitting in the workbench UI.
	 *
	 * @see IWorkbenchWindowActionDelegate#run
	 */
	@Override
	public final void run() {
		// Execute old toolchain on new input file(s)
		final IToolchainData<RunDefinition> toolchain = getLastToolchainData();

		if (toolchain == null) {
			MessageDialog.openError(mWorkbenchWindow.getShell(), "Error Occurred", "There is no old toolchain");
			return;
		}

		final File[] inputFiles = getInputFilesFromUser("Select input file...");
		if (inputFiles == null || inputFiles.length == 0) {
			return;
		}

		final BasicToolchainJob tcj = new GuiRerunFreshToolchainJob("Processing Toolchain", mCore, mController, mLogger,
				toolchain, inputFiles);
		tcj.schedule();

	}
}
