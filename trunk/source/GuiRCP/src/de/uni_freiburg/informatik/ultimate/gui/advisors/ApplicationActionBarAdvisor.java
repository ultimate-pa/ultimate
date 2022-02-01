/*
 * Copyright (C) 2015 Christian Ortolf
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.gui.advisors;

import org.eclipse.jface.action.ICoolBarManager;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.action.ToolBarManager;
import org.eclipse.swt.SWT;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;
import org.eclipse.ui.application.ActionBarAdvisor;
import org.eclipse.ui.application.IActionBarConfigurer;

import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.actions.CancelToolchainAction;
import de.uni_freiburg.informatik.ultimate.gui.actions.LoadSettingsAction;
import de.uni_freiburg.informatik.ultimate.gui.actions.LoadSourceFilesAction;
import de.uni_freiburg.informatik.ultimate.gui.actions.ResetAndRedoToolChainAction;
import de.uni_freiburg.informatik.ultimate.gui.actions.ResetAndRedoToolChainNewTCAction;
import de.uni_freiburg.informatik.ultimate.gui.actions.ResetAndRedoToolChainOldTCAction;
import de.uni_freiburg.informatik.ultimate.gui.actions.ResetSettingsAction;
import de.uni_freiburg.informatik.ultimate.gui.actions.SaveSettingsAction;

/**
 * The class that handles the actions and fills the action bars.
 *
 * @author Christian Ortolf
 *
 */
public class ApplicationActionBarAdvisor extends ActionBarAdvisor {

	private final ICore<RunDefinition> mCore;
	private final GuiController mController;
	private final ILogger mLogger;

	private IWorkbenchAction mExitAction;
	private IWorkbenchAction mAboutAction;
	private IWorkbenchAction mPreferenceAction;

	// custom actions
	private IWorkbenchAction mLoadSourceFiles;
	private IWorkbenchAction mResetAndReRun;
	private IWorkbenchAction mResetAndReRunNewTC;
	private IWorkbenchAction mResetAndReRunOldTC;
	private IWorkbenchAction mLoadSettings;
	private IWorkbenchAction mSaveSettings;
	private IWorkbenchAction mResetSettings;
	private IWorkbenchAction mCancelToolchain;

	public ApplicationActionBarAdvisor(final IActionBarConfigurer configurer, final ICore<RunDefinition> icc,
			final GuiController controller, final ILogger logger) {
		super(configurer);
		mCore = icc;
		mController = controller;
		mLogger = logger;
	}

	/**
	 * Called by Workbench to create our actions.
	 *
	 * @param window
	 *            the workbench window we are in
	 */
	@Override
	protected final void makeActions(final IWorkbenchWindow window) {
		mExitAction = registerAction(ActionFactory.QUIT.create(window));
		mAboutAction = registerAction(ActionFactory.ABOUT.create(window));
		mPreferenceAction = registerAction(ActionFactory.PREFERENCES.create(window));

		mLoadSourceFiles = registerAction(new LoadSourceFilesAction(window, mCore, mController, mLogger));
		mResetAndReRun = registerAction(new ResetAndRedoToolChainAction(window, mCore, mController, mLogger));
		mResetAndReRunNewTC = registerAction(new ResetAndRedoToolChainNewTCAction(window, mCore, mController, mLogger));
		mResetAndReRunOldTC = registerAction(new ResetAndRedoToolChainOldTCAction(window, mCore, mController, mLogger));
		mLoadSettings = registerAction(new LoadSettingsAction(window, mCore));
		mSaveSettings = registerAction(new SaveSettingsAction(window, mCore));
		mResetSettings = registerAction(new ResetSettingsAction(mCore));
		mCancelToolchain = registerAction(new CancelToolchainAction(window, mController, mLogger));
	}

	private IWorkbenchAction registerAction(final IWorkbenchAction action) {
		register(action);
		return action;
	}

	/**
	 * called by workbench the menu.
	 *
	 * @param menuBar
	 */
	@Override
	protected void fillMenuBar(final IMenuManager menuBar) {
		final MenuManager fileMenu = new MenuManager("&File", "file");

		fileMenu.add(mLoadSourceFiles);
		// fileMenu.add(openDottyGraphFromFile);

		// fileMenu.add(preferenceAction);
		fileMenu.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
		fileMenu.add(new Separator());
		fileMenu.add(mExitAction);

		final MenuManager settingsMenu = new MenuManager("&Settings", "settings");
		settingsMenu.add(mPreferenceAction);
		settingsMenu.add(new Separator());
		settingsMenu.add(mLoadSettings);
		settingsMenu.add(mSaveSettings);
		settingsMenu.add(mResetSettings);
		settingsMenu.add(mCancelToolchain);

		final MenuManager helpMenu = new MenuManager("&Help", "help");
		helpMenu.add(mAboutAction);

		menuBar.add(fileMenu);
		menuBar.add(settingsMenu);
		menuBar.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
		menuBar.add(helpMenu);

	}

	@Override
	protected void fillCoolBar(final ICoolBarManager coolBar) {
		final IToolBarManager toolBar = new ToolBarManager(SWT.PUSH);
		coolBar.add(toolBar);

		toolBar.add(mLoadSourceFiles);
		toolBar.add(new Separator());
		toolBar.add(mResetAndReRun);
		toolBar.add(mResetAndReRunNewTC);
		toolBar.add(mResetAndReRunOldTC);
		toolBar.add(new Separator());
		toolBar.add(mLoadSettings);
		toolBar.add(mSaveSettings);
		toolBar.add(mResetSettings);
		toolBar.add(mCancelToolchain);
	}
}
