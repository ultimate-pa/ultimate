/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import org.apache.log4j.Logger;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.services.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchain;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.GuiToolchainJob;
import de.uni_freiburg.informatik.ultimate.gui.contrib.PreludeContribution;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IImageKeys;

/**
 * 
 * @author dietsch
 * @version 0.0.1 $LastChangedDate: 2013-10-28 15:45:22 +0100 (Mo, 28 Okt 2013)
 *          $ $LastChangedBy$LastChangedRevision: 10093 $
 */

public class ResetAndRedoToolChainAction extends RunToolchainAction implements IWorkbenchAction {

	private static final String ID = "de.uni_freiburg.informatik.ultimate.gui.ResetAndRedoToolChainAction";
	private static final String LABEL = "Reset and re-execute";

	public ResetAndRedoToolChainAction(final IWorkbenchWindow window, final ICore icore,
			final GuiController controller, Logger logger) {
		super(logger, window, icore, controller,ID,LABEL,IImageKeys.REEXEC);
	}

	/**
	 * ! This is a generated comment ! The action has been activated. The
	 * argument of the method represents the 'real' action sitting in the
	 * workbench UI.
	 * 
	 * @see IWorkbenchWindowActionDelegate#run
	 */
	public final void run() {
		IToolchain tc = mController.getCurrentToolchain();

		if (tc != null) {
			// we have a toolchain that we can rerun
			BasicToolchainJob tcj = new GuiToolchainJob("Processing Toolchain", mCore, mController, mLogger, tc);
			tcj.schedule();
		} else {
			// we dont have a toolchain that we can rerun, but perhaps we can
			// construct one from our preferences
			BasicToolchainJob tcj = getToolchainJobFromPreferences();
			if (tcj == null) {
				// ok, that also didnt work, we give up
				MessageDialog.openError(mWorkbenchWindow.getShell(), "Error Occurred",
						"Please run a toolchain before trying to " + "rerun it.");
				return;
			}
			tcj.schedule();
		}
	}
	
	private BasicToolchainJob getToolchainJobFromPreferences() {
		File[] lastInputFiles = getLastInputFiles();
		if (lastInputFiles == null) {
			return null;
		}

		File prelude = PreludeContribution.getPreludeFile();
		ToolchainData toolchain = getLastToolchainData();

		if (toolchain == null) {
			MessageDialog.openError(mWorkbenchWindow.getShell(), "Error Occurred",
					"Please run a toolchain before trying to " + "rerun it.");
			return null;
		}
		return new GuiToolchainJob("Re-running toolchain from preferences...", mCore, mController, mLogger, toolchain,
				lastInputFiles, prelude == null ? null : new PreludeProvider(prelude.getAbsolutePath(), mLogger));
	}
}
