package de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.core.api.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchWindow;

/**
 * This class implements an Eclipse Job processing a Ultimate toolchain using
 * the methods publicly available from ICore.
 * 
 * @author Christian Simon
 * 
 */
public class ToolchainJob extends Job {

	/**
	 * How do you want the toolchain to be processed? RUN_TOOLCHAIN: Everything
	 * new from the scratch. RERUN_TOOLCHAIN: run old toolchain on old input
	 * files RUN_OLDTOOLCHAIN: run old toolchain on new input files
	 * RUN_NEWTOOLCHAIN: run new toolchain on old input files
	 * 
	 */
	public static enum Chain_Mode {
		RUN_TOOLCHAIN, RUN_NEWTOOLCHAIN, RERUN_TOOLCHAIN, RUN_OLDTOOLCHAIN
	};

	private Chain_Mode m_JobMode;

	private ICore m_Core;
	private IWorkbenchWindow m_Window;
	private File m_InputFile;

	private Toolchain m_Chain;
	private static Logger s_logger = UltimateServices.getInstance().getLogger(
			Activator.s_PLUGIN_ID);
	private PreludeProvider m_PreludeFile;

	/**
	 * Constructor for the new toolchain job to be executed.
	 * 
	 * @param name
	 *            - How do we want to call the job? Will be display in the
	 *            status bar!
	 * @param mCore
	 *            - Reference to currently active Ultimate Core.
	 * @param mWorkbenchWindow
	 *            - Do we have a workbench window? 'null' is fine!
	 * @param mBoogie
	 *            - array of input boogie files
	 * @param mode_arg
	 *            - The desired mode for toolchain execution. See Chain_Mode.
	 * @param preludefile
	 *            - Do we want a prelude file to be passed to the parser?
	 */
	public ToolchainJob(String name, ICore mCore,
			IWorkbenchWindow mWorkbenchWindow, File mBoogie,
			Chain_Mode mode_arg, PreludeProvider preludefile) {
		super(name);
		setUser(true);
		setSystem(false);
		this.m_Core = mCore;
		this.m_Window = mWorkbenchWindow;
		this.m_InputFile = mBoogie;
		this.m_JobMode = mode_arg;
		this.m_PreludeFile = preludefile;
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {

		IStatus returnstatus = Status.OK_STATUS;

		try {
			boolean retval;

			UltimateServices.getInstance().initializeResultMap();
			UltimateServices.getInstance().initializeTranslatorSequence();

			if ((this.m_JobMode == Chain_Mode.RERUN_TOOLCHAIN || this.m_JobMode == Chain_Mode.RUN_OLDTOOLCHAIN)
					&& !this.m_Core.canRerun()) {
				throw new Exception(
						"Rerun called without previous run! Aborting...");
			}
			// all modes requires this
			this.m_Core.resetCore();

			// only RUN_TOOLCHAIN and RUN_OLDTOOLCHAIN require this
			if (this.m_JobMode == Chain_Mode.RUN_TOOLCHAIN
					|| this.m_JobMode == Chain_Mode.RUN_OLDTOOLCHAIN) {
				this.m_Core.setInputFile(m_InputFile);

			}

			// all but RERUN_TOOLCHAIN require this!
			if (this.m_JobMode != Chain_Mode.RERUN_TOOLCHAIN) {
				retval = this.m_Core.initiateParser(this.m_PreludeFile);
				if (!retval)
					throw new Exception();
			}

			// only RUN_TOOLCHAIN and RUN_NEWTOOLCHAIN require this
			if (this.m_JobMode == Chain_Mode.RUN_TOOLCHAIN
					|| this.m_JobMode == Chain_Mode.RUN_NEWTOOLCHAIN) {
				this.m_Chain = this.m_Core.makeToolSelection();
				if (this.m_Chain == null) {
					s_logger.warn("Toolchain selection failed, aborting...");
					return new Status(Status.CANCEL, Activator.s_PLUGIN_ID, "Toolchain selection canceled");
				}
			}

			this.m_Core.letCoreRunParser();

			returnstatus = this.m_Core.processToolchain(monitor);

		} catch (final Exception e) {
			if (m_Window != null) {
				m_Window.getShell().getDisplay().asyncExec(new Runnable() {
					public void run() {
						MessageDialog.openError(m_Window.getShell(),
								"An error occured",
								"Toolchain throws exception: " + e.getMessage());
					}
				});
			} else {
				System.err
						.println("An error occurred, the toolchain has thrown an exception: "
								+ e.getMessage());
			}
			returnstatus = Status.CANCEL_STATUS;
			e.printStackTrace();
		} finally {
			monitor.done();
		}

		return returnstatus;
	}

}
