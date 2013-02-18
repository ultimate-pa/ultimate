package de.uni_freiburg.informatik.ultimate.gui;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import javax.xml.bind.JAXBException;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.gui.advisors.ApplicationWorkbenchAdvisor;
import de.uni_freiburg.informatik.ultimate.gui.dialogs.AnalysisChooseDialog;
import de.uni_freiburg.informatik.ultimate.gui.dialogs.ModelChooseDialog;
import de.uni_freiburg.informatik.ultimate.gui.dialogs.ParserChooseDialog;

import org.apache.log4j.Logger;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;
import org.xml.sax.SAXException;


/**
 * 
 * gui Controller implemnts IController.
 * 
 * on init  the gui is created
 * so a user can choose files he wants to have parse
 * 
 * the other methods will pop up dialogs for the user
 * so he can Controlle  what the core does
 * 
 * @author Christian Ortolf
 *
 */
public class GuiController implements IController {

	public static final String s_PLUGIN_ID = "UltimateGui";//"de.uni_freiburg.informatik.ultimate.gui.GuiController";
	public static final String s_PLUGIN_NAME = "Gui Controller";
	private static Logger m_Logger = UltimateServices.getInstance().getControllerLogger();
	
	/**
	 * a parent shell for Dialog initialisation
	 */
	private Display m_Display;

	/**
	 * a comvariable for useParser() .
	 */
	private volatile ISource m_Parser;

	//private volatile List<ITool> m_Tools;
	
	private volatile Toolchain m_Tools;
	
	private volatile List<String> m_Models;

	
	/**
	 * Initialization of Controller.
	 * gui is created
	 * note that if you call This method  
	 * your thread will block here until the gui is closed
	 * @return the exit code for the application
	 */
	public int init(Object controlledCore) {
		ICore core;
		if (!(controlledCore instanceof ICore)) {
			return -1;
		} else {
			core = (ICore) controlledCore;
		}

		m_Display = PlatformUI.createDisplay();
		//m_Tools = new ArrayList<ITool>();
		
		m_Parser = null;
		m_Models = new ArrayList<String>();
		m_Logger.debug("Creating Workbench ...");
		m_Logger
				.debug("--------------------------------------------------------------------------------");
		int returnCode = -1;
		ApplicationWorkbenchAdvisor advisor = new ApplicationWorkbenchAdvisor(core);
		if (m_Display != null && advisor !=null) {

			try {
				returnCode = PlatformUI.createAndRunWorkbench(m_Display,
						advisor);
				return returnCode;
			} catch (Exception ex) {
				m_Logger.fatal("An exception occured", ex);
				return returnCode;
			}

		} else {
			m_Logger
					.fatal("PlatformUI.createDisplay() delivered null-value, cannot create workbench, exiting...");

		}
		return returnCode;
	}

	public synchronized ISource selectParser(final Collection<ISource> parsers) {
		
		m_Display.syncExec(new Runnable() {
			public void run() {
				Shell shell = new Shell(m_Display);
				m_Parser = new ParserChooseDialog(shell, parsers).open();
			}
		});
		return m_Parser;
	}

	@SuppressWarnings("unchecked")
	public synchronized Toolchain selectTools(final List<ITool> t) {
		return selectTools(t,Collections.EMPTY_LIST);
	}
	
	public synchronized Toolchain selectTools(final List<ITool> t,final List<ITool> previous) {
		m_Display.syncExec(new Runnable() {
			public void run() {
				Shell shell = new Shell(m_Display);
				try {
					m_Tools = new AnalysisChooseDialog(shell, t,previous).open();
				} catch (FileNotFoundException e) {
					MessageDialog.openError(shell,
											"An error occured", "Toolchain XML file was not found.");
						
				} catch (JAXBException e) {
					MessageDialog.openError(shell,
							"An error occured", "Toolchain XML file could not be validated.");
				} catch (SAXException e) {
					MessageDialog.openError(shell,
							"An error occured", "Toolchain XML file could not be properly parsed.");
				}
			}
		});
		return m_Tools;
	}

	public synchronized List<String> selectModel(final List<String> modelNames) {
		
		m_Display.syncExec(new Runnable() {
			public void run() {
				Shell shell = new Shell(m_Display);
				m_Models = new ModelChooseDialog(shell, modelNames,"Choose the model").open();
			}
		});
		return m_Models;
	}	
	
	public String getName() {
		return s_PLUGIN_NAME;
	}

	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	@Override
	public String getLoadPrefName() {
		FileDialog fd = new FileDialog(m_Display.getActiveShell(),SWT.OPEN);
		return fd.open();
	}

	@Override
	public String getSavePrefName() {
		FileDialog fd = new FileDialog(m_Display.getActiveShell(),SWT.SAVE);
		return fd.open();
	}

}
