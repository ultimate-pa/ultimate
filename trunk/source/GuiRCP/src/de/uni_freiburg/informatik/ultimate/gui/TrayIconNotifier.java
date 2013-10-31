package de.uni_freiburg.informatik.ultimate.gui;

import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.events.ShellEvent;
import org.eclipse.swt.events.ShellListener;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.ToolTip;
import org.eclipse.swt.widgets.TrayItem;
import org.eclipse.ui.PlatformUI;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.gui.advisors.ApplicationWorkbenchAdvisor;

public class TrayIconNotifier {

	private ApplicationWorkbenchAdvisor mWorkbenchAdvisor;
	private boolean mIsResultDisplayActive;

	TrayIconNotifier(ApplicationWorkbenchAdvisor workbenchAdvisor) {
		mWorkbenchAdvisor = workbenchAdvisor;
		mIsResultDisplayActive = false;
	}

	public boolean isResultDisplayActive() {
		return mIsResultDisplayActive;
	}

	private boolean isTrayBalloonEnabled() {
		return Platform.getPreferencesService().getBoolean("UltimateCore",
				CorePreferenceInitializer.LABEL_SHOWRESULTNOTIFIERPOPUP,
				CorePreferenceInitializer.VALUE_SHOWRESULTNOTIFIERPOPUP_DEFAULT,
				null);

	}

	void showTrayBalloon(final String shortMessage, final String longMessage,
			final int style) {
		if (!isTrayBalloonEnabled()) {
			return;
		}

		final Display display = PlatformUI.getWorkbench().getDisplay();
		final TrayItem trayItem = mWorkbenchAdvisor.getTrayItem();
		display.asyncExec(new Runnable() {
			@Override
			public void run() {
				final Shell shell = new Shell(display);

				ToolTip toolTip = new ToolTip(shell, SWT.BALLOON | style);
				toolTip.setMessage(longMessage);
				toolTip.setText(shortMessage);
				trayItem.setToolTip(toolTip);
				toolTip.setVisible(true);
				Shell dispshell = display.getActiveShell();
				toolTip.setAutoHide(shell == dispshell);

				if (dispshell != null && dispshell.isVisible()) {
					mIsResultDisplayActive = true;
					MessageDialog.openInformation(shell, shortMessage,
							longMessage);
					mIsResultDisplayActive = false;

				} else {
					toolTip.addSelectionListener(new SelectionListener() {

						@Override
						public void widgetDefaultSelected(SelectionEvent arg0) {
							shell.close();
							shell.dispose();
						}

						@Override
						public void widgetSelected(SelectionEvent arg0) {
							shell.close();
							shell.dispose();
						}

					});
					PlatformUI.getWorkbench().getWorkbenchWindows()[0]
							.getShell().addShellListener(new ShellListener() {

								@Override
								public void shellActivated(ShellEvent e) {
									Shell shell = (Shell) e.getSource();
									shell.removeShellListener(this);
									MessageDialog.openInformation(shell,
											shortMessage, longMessage);
								}

								@Override
								public void shellClosed(ShellEvent e) {
								}

								@Override
								public void shellDeactivated(ShellEvent e) {
								}

								@Override
								public void shellDeiconified(ShellEvent e) {
									Shell shell = (Shell) e.getSource();
									shell.removeShellListener(this);
									MessageDialog.openInformation(shell,
											shortMessage, longMessage);
								}

								@Override
								public void shellIconified(ShellEvent e) {
								}

							});
				}
			}
		});
		display.wake();

	}

}
