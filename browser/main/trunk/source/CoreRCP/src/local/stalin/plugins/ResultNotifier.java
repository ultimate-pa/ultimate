package local.stalin.plugins;

import java.io.IOException;
import java.io.PrintWriter;

import local.stalin.core.api.StalinServices;
import local.stalin.core.coreplugin.Application.Stalin_Mode;

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

public class ResultNotifier {
	private static boolean isGui() {
		return 
			StalinServices.getInstance().getStalinMode() == Stalin_Mode.USEGUI;
	}
	
	private static PrintWriter g_resultWriter = null;
	
	public static void setResultWriter(PrintWriter resultWriter) {
		g_resultWriter = resultWriter;
	}
	
	private static boolean resultDisplayActive = false;
	
	public static boolean isResultDisplayActive() {
		return resultDisplayActive;
	}

	public static void programCorrect() {
		if( isGui() ) {
			final Display display = PlatformUI.getWorkbench().getDisplay();
			display.asyncExec(new Runnable() {
				@Override
				public void run() {
					Shell shell = display.getActiveShell();
					if( shell == null )
						shell = new Shell(display);
					ToolTip tt = new ToolTip(shell,SWT.BALLOON | SWT.ICON_INFORMATION);
					tt.setMessage("Stalin proved your program to be correct!");
					tt.setText("Program is correct");
					mti.setToolTip(tt);
					tt.setVisible(true);
					Shell dispshell = display.getActiveShell();
					tt.setAutoHide(shell == dispshell);
//					if( dispshell == null ) {
//						shell.close();
//						shell.dispose();
//					}
					if( dispshell != null && dispshell.isVisible() ) {
						resultDisplayActive = true;
						MessageDialog.openInformation(shell,"Program is correct",
							"Stalin proved your program to be correct!");
						resultDisplayActive = false;
					} else {
						final Shell tmpshell = shell;
						tt.addSelectionListener(new SelectionListener() {

							@Override
							public void widgetDefaultSelected(
									SelectionEvent arg0) {
								tmpshell.close();
								tmpshell.dispose();
							}

							@Override
							public void widgetSelected(SelectionEvent arg0) {
								tmpshell.close();
								tmpshell.dispose();
							}
							
						});
						PlatformUI.getWorkbench().getWorkbenchWindows()[0].getShell().addShellListener(new ShellListener() {

							@Override
							public void shellActivated(ShellEvent e) {
								Shell shell = (Shell)e.getSource();
								shell.removeShellListener(this);
								MessageDialog.openInformation(shell,"Program is correct",
									"Stalin proved your program to be correct!");
							}

							@Override
							public void shellClosed(ShellEvent e) {}

							@Override
							public void shellDeactivated(ShellEvent e) {}

							@Override
							public void shellDeiconified(ShellEvent e) {
								Shell shell = (Shell)e.getSource();
								shell.removeShellListener(this);
								MessageDialog.openInformation(shell,"Program is correct",
									"Stalin proved your program to be correct!");
							}

							@Override
							public void shellIconified(ShellEvent e) {}
							
						});
					}
				}
			});
			display.wake();
		} else {
			if (g_resultWriter == null) {
				System.err.println();
				System.err.println("RESULT: Stalin proved your program to be correct!");
				if (StalinServices.getInstance().getStalinMode() == 
					Stalin_Mode.INTERACTIVE) {
					System.err.println("Press enter");
					try {
						System.in.read();
					} catch( IOException ignored ) {}
				}
			} else {
				g_resultWriter.println("RESULT: Stalin proved your program to be correct!");
				g_resultWriter.flush();
			}
		}
	}
	
	private static TrayItem mti;
	
	public static void setTrayItem(TrayItem ti) {
		mti = ti;
	}
	
	public static void programIncorrect() {
		if( isGui() ) {
			final Display display = PlatformUI.getWorkbench().getDisplay();
			display.asyncExec(new Runnable() {
				@Override
				public void run() {
					Shell shell = display.getActiveShell();
					if( shell == null )
						shell = new Shell(display);
					ToolTip tt = new ToolTip(shell,SWT.BALLOON | SWT.ICON_WARNING);
					tt.setMessage("Stalin proved your program to be incorrect!");
					tt.setText("Program is incorrect");
					mti.setToolTip(tt);
					tt.setVisible(true);
					Shell dispshell = display.getActiveShell();
					tt.setAutoHide(shell == dispshell);
//					if( dispshell == null ) {
//						shell.close();
//						shell.dispose();
//					}
					if( dispshell != null && dispshell.isVisible() ) {
						resultDisplayActive = true;
						MessageDialog.openInformation(shell,"Program is incorrect",
							"Stalin proved your program to be incorrect!");
						resultDisplayActive = false;
					} else {
						final Shell tmpshell = shell;
						tt.addSelectionListener(new SelectionListener() {

							@Override
							public void widgetDefaultSelected(
									SelectionEvent arg0) {
								tmpshell.close();
								tmpshell.dispose();
							}

							@Override
							public void widgetSelected(SelectionEvent arg0) {
								tmpshell.close();
								tmpshell.dispose();
							}
							
						});
						PlatformUI.getWorkbench().getWorkbenchWindows()[0].getShell().addShellListener(new ShellListener() {

							@Override
							public void shellActivated(ShellEvent e) {
								Shell shell = (Shell)e.getSource();
								shell.removeShellListener(this);
								MessageDialog.openInformation(shell,"Program is incorrect",
									"Stalin proved your program to be incorrect!");
							}

							@Override
							public void shellClosed(ShellEvent e) {}

							@Override
							public void shellDeactivated(ShellEvent e) {}

							@Override
							public void shellDeiconified(ShellEvent e) {
								Shell shell = (Shell)e.getSource();
								shell.removeShellListener(this);
								MessageDialog.openInformation(shell,"Program is incorrect",
									"Stalin proved your program to be incorrect!");
							}

							@Override
							public void shellIconified(ShellEvent e) {}
							
						});
					}
				}
			});
			display.wake();
		} else {
			if (g_resultWriter == null) {
				System.err.println();
				System.err.println("RESULT: Stalin proved your program to be incorrect!");
				if (StalinServices.getInstance().getStalinMode() == 
					Stalin_Mode.INTERACTIVE) {
					System.err.println("Press any key");
					try {
						System.in.read();
					} catch( IOException ignored ) {}
				}
			} else {
				g_resultWriter.println("RESULT: Stalin proved your program to be incorrect!");
				g_resultWriter.flush();
			}
		}
	}
	
	public static void programUnknown(final String text) {
		if( isGui() ) {
			final Display display = PlatformUI.getWorkbench().getDisplay();
			display.asyncExec(new Runnable() {
				@Override
				public void run() {
					Shell shell = display.getActiveShell();
					if( shell == null )
						shell = new Shell(display);
					ToolTip tt = new ToolTip(shell,SWT.BALLOON | SWT.ICON_INFORMATION);
					tt.setMessage("Stalin could not prove your program: " + text);
					tt.setText("Program could not be checked");
					mti.setToolTip(tt);
					tt.setVisible(true);
					Shell dispshell = display.getActiveShell();
					tt.setAutoHide(shell == dispshell);
//					if( dispshell == null ) {
//						shell.close();
//						shell.dispose();
//					}
					if( dispshell != null && dispshell.isVisible() ) {
						resultDisplayActive = true;
						MessageDialog.openInformation(shell,"Program could not be checked",
								"Stalin could not prove your program: " + text);
						resultDisplayActive = false;
					} else {
						final Shell tmpshell = shell;
						tt.addSelectionListener(new SelectionListener() {

							@Override
							public void widgetDefaultSelected(
									SelectionEvent arg0) {
								tmpshell.close();
								tmpshell.dispose();
							}

							@Override
							public void widgetSelected(SelectionEvent arg0) {
								tmpshell.close();
								tmpshell.dispose();
							}
							
						});
						PlatformUI.getWorkbench().getWorkbenchWindows()[0].getShell().addShellListener(new ShellListener() {

							@Override
							public void shellActivated(ShellEvent e) {
								Shell shell = (Shell)e.getSource();
								shell.removeShellListener(this);
								MessageDialog.openInformation(shell,"Program could not be checked",
										"Stalin could not prove your program: " + text);
							}

							@Override
							public void shellClosed(ShellEvent e) {}

							@Override
							public void shellDeactivated(ShellEvent e) {}

							@Override
							public void shellDeiconified(ShellEvent e) {
								Shell shell = (Shell)e.getSource();
								shell.removeShellListener(this);
								MessageDialog.openInformation(shell,"Program could not be checked",
										"Stalin could not prove your program: " + text);
							}

							@Override
							public void shellIconified(ShellEvent e) {}
							
						});
					}
				}
			});
			display.wake();
		} else {
			if (g_resultWriter == null) {
				System.err.println();
				System.err.println("RESULT: Stalin could not prove your program: " + text);
				if (StalinServices.getInstance().getStalinMode() == 
					Stalin_Mode.INTERACTIVE) {
					System.err.println("Press any key");
					try {
						System.in.read();
					} catch( IOException ignored ) {}
				}
			} else {
				g_resultWriter.println("RESULT: Stalin could not prove your program: " + text);
				g_resultWriter.flush();
			}
		}
	}
}
