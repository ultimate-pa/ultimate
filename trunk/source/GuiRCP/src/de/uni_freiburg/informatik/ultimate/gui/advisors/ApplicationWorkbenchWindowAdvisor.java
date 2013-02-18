package de.uni_freiburg.informatik.ultimate.gui.advisors;

import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IImageKeys;
import de.uni_freiburg.informatik.ultimate.plugins.ResultNotifier;

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
 * @author ortolf
 *
 */
public class ApplicationWorkbenchWindowAdvisor extends WorkbenchWindowAdvisor {

	private final ICore icc;

	public ApplicationWorkbenchWindowAdvisor(
			IWorkbenchWindowConfigurer configurer, ICore icc) {
		super(configurer);
		this.icc = icc;
	}

	public ActionBarAdvisor createActionBarAdvisor(
			IActionBarConfigurer configurer) {
		return new ApplicationActionBarAdvisor(configurer, icc);
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
		/* greetz to Mr. Ortolf: Tray items are sh*** ;-) */
		final IWorkbenchWindow window = getWindowConfigurer().getWindow();
		trayItem = initTaskItem(window);
		if (trayItem != null) {
			hookMinimized(window);
		}
	}

	private TrayItem trayItem;

	private Image trayImage;

	private void hookMinimized(final IWorkbenchWindow window) {
		window.getShell().addShellListener(new ShellAdapter() {
			public void shellIconified(ShellEvent e) {
				if( !ResultNotifier.isResultDisplayActive() )
					window.getShell().setVisible(false);
			}
		});
		trayItem.addListener(SWT.DefaultSelection, new Listener() {
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

	private TrayItem initTaskItem(IWorkbenchWindow window) {
		final Tray tray = window.getShell().getDisplay().getSystemTray();
		if (tray == null)
			return null;
		TrayItem trayItem = new TrayItem(tray, SWT.NONE);
		ImageDescriptor id = AbstractUIPlugin.imageDescriptorFromPlugin(
				GuiController.s_PLUGIN_ID, IImageKeys.TRAYICON);
		trayImage = id.createImage();
		trayItem.setImage(trayImage);
		trayItem.setToolTipText("Ultimate Model Checker");
		ResultNotifier.setTrayItem(trayItem);
		final Menu menu = new Menu (window.getShell(), SWT.POP_UP);
		final MenuItem exit = new MenuItem(menu,SWT.PUSH);
		exit.setText("Exit Ultimate");
		exit.addListener(SWT.Selection, new Listener() {
			public void handleEvent(Event event) {
				exit.dispose();
				menu.dispose();
				getWindowConfigurer().getWorkbenchConfigurer().getWorkbench().close();
			}
		});
		trayItem.addListener (SWT.MenuDetect, new Listener () {
			public void handleEvent (Event event) {
				menu.setVisible (true);
			}
		});

		return trayItem;
	}

	/*
	 * private void hookPopupMenu(final IWorkbenchWindow window ){
	 * trayItem.addListener(SWT.MenuDetect, new Listener(){ public void
	 * handleEvent(Event event){ MenuManager trayMenu= new MenuManager(); Menu
	 * menu= trayMenu.createContextMenu(window.getShell());
	 * 
	 * actionBarAdvisor. } });
	 *  }
	 */

	public void postWindowClose() {
		super.postWindowClose();

	}

	public void dispose() {
		if (trayImage != null) {
			trayImage.dispose();
			trayItem.dispose();
		}
	}

}
