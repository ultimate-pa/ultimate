package de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.wizards;

import java.lang.reflect.InvocationTargetException;
import java.net.URI;

import de.uni_freiburg.informatik.ultimate.dev.eclipse.templates.UltimatePluginData;


import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExecutableExtension;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.dialogs.WizardNewProjectCreationPage;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.wizards.newresource.BasicNewProjectResourceWizard;

public class NewUltimatePluginWizard extends Wizard implements INewWizard,
		IExecutableExtension {

	private static final String PAGE_NAME = "Ultimate Plugin";
	private static final String WIZARD_NAME = "New Ultimate Plugin Project";
	private static final String DESCRIPTION = "This wizard creates a new Ultimate Plugin Project.";

	private WizardNewProjectCreationPage m_pageOne;
	private NewUltimatePluginDetailsPage m_pageTwo;
	private IConfigurationElement m_configurationElement;

	public NewUltimatePluginWizard() {
		setWindowTitle(IMessages.WIZARD_TITLE);
	}

	/**
	 * This method is called when 'Finish' button is pressed in the wizard.
	 * Creates an operation and runs it using wizard as execution context.
	 */
	@Override
	public boolean performFinish() {
		final String name = m_pageOne.getProjectName();
		URI tmp = null;
		if (!m_pageOne.useDefaults()) {
			tmp = m_pageOne.getLocationURI();
		} // else location == null
		final URI location = tmp;

		final UltimatePluginData data = m_pageTwo.getUltimatePluginData();
		IRunnableWithProgress op = new IRunnableWithProgress() {
			public void run(IProgressMonitor monitor)
					throws InvocationTargetException {
				try {
					doFinish(name, data, location, monitor);
				} catch (CoreException e) {
					throw new InvocationTargetException(e);
				} finally {
					monitor.done();
				}
			}
		};
		try {
			getContainer().run(true, false, op);
		} catch (InterruptedException e) {
			return false;
		} catch (InvocationTargetException e) {
			Throwable realException = e.getTargetException();
			MessageDialog.openError(getShell(), "Error", realException
					.getMessage());
			return false;
		}
		return true;
	}

	/**
	 * The worker method. It will create the project and run file generators and
	 * finally open the editor on the newly main class
	 * @param name 
	 */
	private void doFinish(String name, UltimatePluginData data, URI location,
			IProgressMonitor monitor) throws CoreException {
		// create the project. Uses UltimatePluginSupport class to do the work
		monitor.beginTask("Creating " + data.getPluginName(), 2);
		IProject project = UltimatePluginSupport.createProject(name, location, data, monitor);

		// update perspective to debug perspective
		BasicNewProjectResourceWizard.updatePerspective(m_configurationElement);
		monitor.worked(1);
		// open the main class right away
		monitor.setTaskName("Opening file for editing...");
		final IFile file = project.getFolder(
				UltimatePluginSupport.PACKAGE_PREFIX_PATH + "/"
						+ data.getTypeString() + "/"
						+ data.getPluginName().toLowerCase()).getFile(
				data.getPluginName() + ".java");
		getShell().getDisplay().asyncExec(new Runnable() {
			public void run() {
				IWorkbenchPage page = PlatformUI.getWorkbench()
						.getActiveWorkbenchWindow().getActivePage();
				try {
					IDE.openEditor(page, file, true);
				} catch (PartInitException e) {
				}
			}
		});
		monitor.worked(1);
	}

	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setInitializationData(IConfigurationElement config,
			String propertyName, Object data) throws CoreException {
		m_configurationElement = config;
	}

	@Override
	public void addPages() {
		super.addPages();

		m_pageOne = new WizardNewProjectCreationPage(PAGE_NAME);
		m_pageOne.setTitle(WIZARD_NAME);
		m_pageOne.setDescription(DESCRIPTION);
		addPage(m_pageOne);
		
		m_pageTwo = new NewUltimatePluginDetailsPage(PAGE_NAME);
		m_pageTwo.setTitle(WIZARD_NAME);
		m_pageTwo.setDescription(DESCRIPTION);
		addPage(m_pageTwo);
	}

}
