/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.preferences.IPreferencesService;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.gui.advisors.ApplicationWorkbenchAdvisor;

public class TrayIconNotifier {

	private final ApplicationWorkbenchAdvisor mWorkbenchAdvisor;
	private final boolean mIsResultDisplayActive;

	TrayIconNotifier(ApplicationWorkbenchAdvisor workbenchAdvisor) {
		mWorkbenchAdvisor = workbenchAdvisor;
		mIsResultDisplayActive = false;
	}

	public boolean isResultDisplayActive() {
		return mIsResultDisplayActive;
	}

	private boolean isTrayBalloonEnabled() {
		final IPreferencesService prefService = Platform.getPreferencesService();
		if (prefService == null) {
			return false;
		}
		return prefService.getBoolean("UltimateCore", CorePreferenceInitializer.LABEL_SHOWRESULTNOTIFIERPOPUP,
				CorePreferenceInitializer.VALUE_SHOWRESULTNOTIFIERPOPUP_DEFAULT, null);
	}

	void showTrayBalloon(final String shortMessage, final String longMessage, final int style) {
		if (!isTrayBalloonEnabled()) {
			return;
		}
//		final Display display = PlatformUI.getWorkbench().getDisplay();
//		final TrayItem trayItem = mWorkbenchAdvisor.getTrayItem();
		// No tray icon => cannot display result in tray icon.
//		if (trayItem == null)
//			return;
//		display.asyncExec(new Runnable() {
//			@Override
//			public void run() {
//				final Shell shell = new Shell(display);
//
//				ToolTip toolTip = new ToolTip(shell, SWT.BALLOON | style);
//				toolTip.setMessage(longMessage);
//				toolTip.setText(shortMessage);
//				trayItem.setToolTip(toolTip);
//				toolTip.setVisible(true);
//				Shell dispshell = display.getActiveShell();
//				toolTip.setAutoHide(shell == dispshell);
//
//				if (dispshell != null && dispshell.isVisible()) {
//					mIsResultDisplayActive = true;
//					MessageDialog.openInformation(shell, shortMessage, longMessage);
//					mIsResultDisplayActive = false;
//
//				} else {
//					toolTip.addSelectionListener(new SelectionListener() {
//
//						@Override
//						public void widgetDefaultSelected(SelectionEvent arg0) {
//							shell.close();
//							shell.dispose();
//						}
//
//						@Override
//						public void widgetSelected(SelectionEvent arg0) {
//							shell.close();
//							shell.dispose();
//						}
//
//					});
//					PlatformUI.getWorkbench().getWorkbenchWindows()[0].getShell().addShellListener(new ShellListener() {
//
//						@Override
//						public void shellActivated(ShellEvent e) {
//							Shell shell = (Shell) e.getSource();
//							shell.removeShellListener(this);
//							MessageDialog.openInformation(shell, shortMessage, longMessage);
//						}
//
//						@Override
//						public void shellClosed(ShellEvent e) {
//						}
//
//						@Override
//						public void shellDeactivated(ShellEvent e) {
//						}
//
//						@Override
//						public void shellDeiconified(ShellEvent e) {
//							Shell shell = (Shell) e.getSource();
//							shell.removeShellListener(this);
//							MessageDialog.openInformation(shell, shortMessage, longMessage);
//						}
//
//						@Override
//						public void shellIconified(ShellEvent e) {
//						}
//
//					});
//				}
//			}
//		});
//		display.wake();

	}

}
