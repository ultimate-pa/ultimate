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
package de.uni_freiburg.informatik.ultimate.gui.advisors;

import org.eclipse.core.runtime.Platform;
import org.eclipse.ui.application.IWorkbenchConfigurer;
import org.eclipse.ui.application.IWorkbenchWindowConfigurer;
import org.eclipse.ui.application.WorkbenchAdvisor;
import org.eclipse.ui.application.WorkbenchWindowAdvisor;

import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.TrayIconNotifier;
import de.uni_freiburg.informatik.ultimate.gui.UltimateDefaultPerspective;

/**
 *
 * @author Ortolf
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ApplicationWorkbenchAdvisor extends WorkbenchAdvisor {

	private ILogger mLogger;
	private ICore<RunDefinition> mCore;
	private ApplicationWorkbenchWindowAdvisor mApplicationWorkbenchWindowAdvisor;
	private TrayIconNotifier mTrayIconNotifier;
	private GuiController mController;

	public void init(final ICore<RunDefinition> icc, final TrayIconNotifier notifier, final GuiController controller,
			final ILogger logger) {
		mLogger = logger;
		mCore = icc;
		mTrayIconNotifier = notifier;
		mController = controller;
	}

	@Override
	public WorkbenchWindowAdvisor createWorkbenchWindowAdvisor(final IWorkbenchWindowConfigurer configurer) {
		mLogger.debug("Requesting WorkbenchWindowAdvisor");

		if (mCore == null || mTrayIconNotifier == null) {
			throw new IllegalStateException("mCore or mTrayIconNotifier are null; maybe you did not call init()?");
		}

		if (mApplicationWorkbenchWindowAdvisor == null) {
			mLogger.debug("Creating WorkbenchWindowAdvisor...");
			mApplicationWorkbenchWindowAdvisor =
					new ApplicationWorkbenchWindowAdvisor(configurer, mCore, mTrayIconNotifier, mController, mLogger);
		}
		return mApplicationWorkbenchWindowAdvisor;
	}

	@Override
	public String getInitialWindowPerspectiveId() {
		return UltimateDefaultPerspective.ID;
	}

	@Override
	public void initialize(final IWorkbenchConfigurer configurer) {
		super.initialize(configurer);
		configurer.setSaveAndRestore(!Platform.inDevelopmentMode());
	}
}
