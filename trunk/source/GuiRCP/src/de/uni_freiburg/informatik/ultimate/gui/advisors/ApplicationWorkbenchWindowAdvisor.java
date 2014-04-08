package de.uni_freiburg.informatik.ultimate.gui.advisors;

import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.TrayIconNotifier;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IImageKeys;
import de.uni_freiburg.informatik.ultimate.gui.preferencepages.UltimatePreferencePageFactory;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ShellAdapter;
import org.eclipse.swt.events.ShellEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Tray;
import org.eclipse.swt.widgets.TrayItem;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.application.ActionBarAdvisor;
import org.eclipse.ui.application.IActionBarConfigurer;
import org.eclipse.ui.application.IWorkbenchWindowConfigurer;
import org.eclipse.ui.application.WorkbenchWindowAdvisor;
import org.eclipse.ui.plugin.AbstractUIPlugin;

/**
 * 
 * @author dietsch
 * 
 */
public class ApplicationWorkbenchWindowAdvisor extends WorkbenchWindowAdvisor {

	private final ICore mCore;
	private final IController mController;
	private TrayItem mTrayItem;
	private Image mTrayImage;
	private TrayIconNotifier mTrayIconNotifier;

	public ApplicationWorkbenchWindowAdvisor(
			IWorkbenchWindowConfigurer configurer, ICore icc,
			TrayIconNotifier notifier, IController controller) {
		super(configurer);
		mCore = icc;
		mTrayIconNotifier = notifier;
		mController = controller;

	}

	public TrayItem getTrayItem() {
		return mTrayItem;
	}

	public ActionBarAdvisor createActionBarAdvisor(
			IActionBarConfigurer configurer) {
		return new ApplicationActionBarAdvisor(configurer, mCore, mController);
	}

	public void preWindowOpen() {
		IWorkbenchWindowConfigurer configurer = getWindowConfigurer();
		configurer.setTitle("Ultimate");
		configurer.setInitialSize(new Point(1024, 768));
		configurer.setShowMenuBar(true);
		configurer.setShowCoolBar(true);
		configurer.setShowStatusLine(true);
		configurer.setShowPerspectiveBar(true);
		configurer.setShowProgressIndicator(true);

	}

	public void postWindowOpen() {
		super.postWindowOpen();
		final IWorkbenchWindow window = getWindowConfigurer().getWindow();
		if (initTaskItem(window)) {
			hookMinimized(window);
		}
		new UltimatePreferencePageFactory(mCore).createPreferencePages();
	}

	public void dispose() {
		if (mTrayImage != null) {
			mTrayImage.dispose();

		}
		if (mTrayItem != null) {
			mTrayItem.dispose();
		}
	}

	private void hookMinimized(final IWorkbenchWindow window) {
		window.getShell().addShellListener(new ShellAdapter() {
			public void shellIconified(ShellEvent e) {
				if (!mTrayIconNotifier.isResultDisplayActive()) {
					window.getShell().setVisible(false);
				}
			}
		});
		mTrayItem.addListener(SWT.DefaultSelection, new Listener() {
			public void handleEvent(Event e) {
				Shell shell = window.getShell();
				if (!shell.isVisible()) {
					shell.setMinimized(false);
					shell.setVisible(true);
					shell.setActive();
					shell.setFocus();
				} else {
					shell.forceActive();
					shell.setFocus();
				}
			}
		});
	}

	/**
	 * Returns true if the tray icon was initialized successfully, false
	 * otherwise
	 * 
	 * @param window
	 * @return
	 */
	private boolean initTaskItem(IWorkbenchWindow window) {
		final Tray tray = window.getShell().getDisplay().getSystemTray();
		if (tray == null) {
			return false;
		}
		mTrayItem = new TrayItem(tray, SWT.NONE);
		ImageDescriptor id = AbstractUIPlugin.imageDescriptorFromPlugin(
				GuiController.sPLUGINID, IImageKeys.TRAYICON);
		mTrayImage = id.createImage();
		mTrayItem.setImage(mTrayImage);
		mTrayItem.setToolTipText("Ultimate Model Checker");

		final Menu menu = new Menu(window.getShell(), SWT.POP_UP);
		final MenuItem exit = new MenuItem(menu, SWT.PUSH);
		exit.setText("Exit Ultimate");
		exit.addListener(SWT.Selection, new Listener() {
			public void handleEvent(Event event) {
				exit.dispose();
				menu.dispose();
				getWindowConfigurer().getWorkbenchConfigurer().getWorkbench()
						.close();
			}
		});
		mTrayItem.addListener(SWT.MenuDetect, new Listener() {
			public void handleEvent(Event event) {
				menu.setVisible(true);
			}
		});

		return true;
	}

}
