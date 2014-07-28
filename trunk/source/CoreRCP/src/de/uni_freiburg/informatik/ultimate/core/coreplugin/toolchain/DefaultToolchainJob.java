package de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain;

import java.io.File;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchain;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;

/**
 * This class implements an Eclipse Job processing a Ultimate toolchain using
 * the methods publicly available from ICore.
 * 
 * @author Christian Simon
 * 
 */
public class DefaultToolchainJob extends BasicToolchainJob {

	private File mInputFile;

	/**
	 * Constructor for the new toolchain job to be executed.
	 * 
	 * @param name
	 *            - How do we want to call the job? Will be display in the
	 *            status bar!
	 * @param core
	 *            - Reference to currently active Ultimate Core.
	 * @param mode
	 *            - The desired mode for toolchain execution. See Chain_Mode.
	 * @param boogieFiles
	 *            - array of input boogie files
	 * @param preludefile
	 *            - Do we want a prelude file to be passed to the parser?
	 * @param logger
	 *            The logger that is used to print information about the
	 *            toolchain execution
	 */
	public DefaultToolchainJob(String name, ICore core, IController controller, ChainMode mode, File boogieFiles,
			PreludeProvider preludefile, Logger logger) {
		super(name, core, controller, mode, logger);
		setUser(true);
		setSystem(false);

		mInputFile = boogieFiles;
		mPreludeFile = preludefile;

	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {

		// TODO: This method needs to be refactored (also for sister class
		// ExternalParserToolchainJob)
		IStatus returnstatus = Status.OK_STATUS;
		monitor.beginTask(getName(), IProgressMonitor.UNKNOWN);
		IToolchain currentToolchain = null;

		try {
			boolean retval;

			monitor.worked(1);

			if ((mJobMode == ChainMode.RERUN_TOOLCHAIN || mJobMode == ChainMode.RUN_OLDTOOLCHAIN)) {
				throw new Exception("Rerun currently unsupported! Aborting...");
			}
			// all modes requires this
			currentToolchain = mCore.requestToolchain();

			currentToolchain.resetCore();
			monitor.worked(1);

			// only RUN_TOOLCHAIN and RUN_OLDTOOLCHAIN require this
			if (mJobMode == ChainMode.RUN_TOOLCHAIN || mJobMode == ChainMode.RUN_OLDTOOLCHAIN) {
				currentToolchain.setInputFile(mInputFile);

			}
			monitor.worked(1);

			// all but RERUN_TOOLCHAIN require this!
			if (mJobMode != ChainMode.RERUN_TOOLCHAIN) {
				retval = currentToolchain.initializeParser(mPreludeFile);
				if (!retval) {
					throw new Exception();
				}

			}
			monitor.worked(1);

			// only RUN_TOOLCHAIN and RUN_NEWTOOLCHAIN require this
			if (mJobMode == ChainMode.RUN_TOOLCHAIN || mJobMode == ChainMode.RUN_NEWTOOLCHAIN) {
				mChain = currentToolchain.makeToolSelection();
				if (mChain == null) {
					mLogger.warn("Toolchain selection failed, aborting...");
					return new Status(Status.CANCEL, Activator.s_PLUGIN_ID, "Toolchain selection canceled");
				}
				setServices(mChain.getServices());
			}
			monitor.worked(1);

			currentToolchain.runParser();
			monitor.worked(1);

			returnstatus = currentToolchain.processToolchain(monitor);

		} catch (final Throwable e) {
			mLogger.fatal(String.format("The toolchain threw an exception: %s", e.getMessage()));
			mLogger.fatal(e);
			mController.displayException("The toolchain threw an exception", e);
			returnstatus = Status.CANCEL_STATUS;
			String idOfCore = Activator.s_PLUGIN_ID;
			if (mServices != null) {
				mServices.getResultService().reportResult(idOfCore, new ExceptionOrErrorResult(idOfCore, e));
			} 
		} finally {
			monitor.done();
			logResults();
			mCore.releaseToolchain(currentToolchain);
		}

		return returnstatus;
	}

}
