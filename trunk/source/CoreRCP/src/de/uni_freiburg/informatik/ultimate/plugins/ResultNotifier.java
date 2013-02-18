package de.uni_freiburg.informatik.ultimate.plugins;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.List;

import org.eclipse.core.runtime.preferences.ConfigurationScope;
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

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Application.Ultimate_Mode;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.IPreferenceConstants;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;

public class ResultNotifier {
	
	private static final int NORESULT	= 0;
	private static final int CORRECT	= 1;
	private static final int UNPROVABLE = 2;
	private static final int TIMEOUT	= 3;
	private static final int INCORRECT	= 4;
	private static final int SYNTAXERROR= 5;
	
	private static boolean useGui() {	
		boolean useGui = 
				UltimateServices.getInstance().getUltimateMode() == Ultimate_Mode.USEGUI;
		useGui = useGui && 
				ConfigurationScope.INSTANCE.getNode(Activator.s_PLUGIN_ID).getBoolean(
						IPreferenceConstants.s_NAME_SHOWRESULTNOTIFIERPOPUP,
						IPreferenceConstants.s_VALUE_SHOWRESULTNOTIFIERPOPUP_DEFAULT);
		return useGui;
			
	}
	
	private static PrintWriter g_resultWriter = null;
	
	public static void setResultWriter(PrintWriter resultWriter) {
		g_resultWriter = resultWriter;
	}
	
	private static boolean resultDisplayActive = false;
	
	public static boolean isResultDisplayActive() {
		return resultDisplayActive;
	}

	public static void processResults() {
		int toolchainResult = ResultNotifier.NORESULT;
		String description = "Toolchain returned no Result.";
		
		for(List<IResult> PluginResults: UltimateServices.getInstance().getResultMap().values()) {
			for (IResult result: PluginResults) {
				if (result instanceof SyntaxErrorResult) {
					toolchainResult = ResultNotifier.SYNTAXERROR;
					description = result.getShortDescription();
				} else if (result instanceof UnprovableResult) {
					if (toolchainResult < ResultNotifier.UNPROVABLE)
						toolchainResult = ResultNotifier.UNPROVABLE;
					description = "unable to determine feasibility of some traces";
				} else if (result instanceof CounterExampleResult) {
					if (toolchainResult < ResultNotifier.INCORRECT)
						toolchainResult = ResultNotifier.INCORRECT;
				} else if (result instanceof PositiveResult) {
					if (toolchainResult < ResultNotifier.CORRECT)
						toolchainResult = ResultNotifier.CORRECT;
				} else if (result instanceof TimeoutResult) {
					if (toolchainResult < ResultNotifier.TIMEOUT)
						toolchainResult = ResultNotifier.TIMEOUT;
					description = "Timeout";
				}
			}
		}
		switch (toolchainResult) {
		case SYNTAXERROR:
			ResultNotifier.programUnknown(description);
			break;
		case UNPROVABLE:
			ResultNotifier.programUnknown(description);
			break;
		case INCORRECT:
			ResultNotifier.programIncorrect();
			break;
		case CORRECT:
			ResultNotifier.programCorrect();
			break;
		case TIMEOUT:
			ResultNotifier.programUnknown(description);
			break;
		case NORESULT:
			ResultNotifier.programUnknown(description);
			break;
		default:
			throw new AssertionError("unknown result");
		}
	}
	
	public static void programCorrect() {
		if( useGui() ) {
			final Display display = PlatformUI.getWorkbench().getDisplay();
			display.asyncExec(new Runnable() {
				@Override
				public void run() {
					Shell shell = new Shell(display);
//					Shell shell = display.getActiveShell();
//					if( shell == null )
//						shell = new Shell(display);
					ToolTip tt = new ToolTip(shell,SWT.BALLOON | SWT.ICON_INFORMATION);
					tt.setMessage("Ultimate proved your program to be correct!");
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
							"Ultimate proved your program to be correct!");
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
									"Ultimate proved your program to be correct!");
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
									"Ultimate proved your program to be correct!");
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
				System.err.println("RESULT: Ultimate proved your program to be correct!");
				if (UltimateServices.getInstance().getUltimateMode() == 
					Ultimate_Mode.INTERACTIVE) {
					System.err.println("Press enter");
					try {
						System.in.read();
					} catch( IOException ignored ) {}
				}
			} else {
				g_resultWriter.println("RESULT: Ultimate proved your program to be correct!");
				g_resultWriter.flush();
			}
		}
	}
	
	private static TrayItem mti;
	
	public static void setTrayItem(TrayItem ti) {
		mti = ti;
	}
	
	public static void programIncorrect() {
		if( useGui() ) {
			final Display display = PlatformUI.getWorkbench().getDisplay();
			display.asyncExec(new Runnable() {
				@Override
				public void run() {
					Shell shell = new Shell(display);
//					Shell shell = display.getActiveShell();
//					if( shell == null )
//						shell = new Shell(display);
					ToolTip tt = new ToolTip(shell,SWT.BALLOON | SWT.ICON_WARNING);
					tt.setMessage("Ultimate proved your program to be incorrect!");
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
							"Ultimate proved your program to be incorrect!");
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
									"Ultimate proved your program to be incorrect!");
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
									"Ultimate proved your program to be incorrect!");
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
				System.err.println("RESULT: Ultimate proved your program to be incorrect!");
				if (UltimateServices.getInstance().getUltimateMode() == 
					Ultimate_Mode.INTERACTIVE) {
					System.err.println("Press any key");
					try {
						System.in.read();
					} catch( IOException ignored ) {}
				}
			} else {
				g_resultWriter.println("RESULT: Ultimate proved your program to be incorrect!");
				g_resultWriter.flush();
			}
		}
	}
	
	public static void programUnknown(final String text) {
		if( useGui() ) {
			final Display display = PlatformUI.getWorkbench().getDisplay();
			display.asyncExec(new Runnable() {
				@Override
				public void run() {
					Shell shell = new Shell(display);
//					if( shell == null )
//						shell = new Shell(display);
					ToolTip tt = new ToolTip(shell,SWT.BALLOON | SWT.ICON_INFORMATION);
					tt.setMessage("Ultimate could not prove your program: " + text);
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
//						MessageBox()
						MessageDialog.openInformation(shell,"Program could not be checked",
								"Ultimate could not prove your program: " + text);
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
										"Ultimate could not prove your program: " + text);
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
										"Ultimate could not prove your program: " + text);
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
				System.err.println("RESULT: Ultimate could not prove your program: " + text);
				if (UltimateServices.getInstance().getUltimateMode() == 
					Ultimate_Mode.INTERACTIVE) {
					System.err.println("Press any key");
					try {
						System.in.read();
					} catch( IOException ignored ) {}
				}
			} else {
				g_resultWriter.println("RESULT: Ultimate could not prove your program: " + text);
				g_resultWriter.flush();
			}
		}
	}
}
