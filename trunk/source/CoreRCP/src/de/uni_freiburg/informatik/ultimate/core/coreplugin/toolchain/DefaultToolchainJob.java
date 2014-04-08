package de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain;

import java.io.File;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

import de.uni_freiburg.informatik.ultimate.core.api.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
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
	 * @param mWorkbenchWindow
	 *            - Do we have a workbench window? 'null' is fine!
	 */
	public DefaultToolchainJob(String name, ICore core, IController controller, ChainMode mode, File boogieFiles,
			PreludeProvider preludefile) {
		super(name, core, controller, mode);
		setUser(true);
		setSystem(false);

		mInputFile = boogieFiles;
		mPreludeFile = preludefile;

	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {

		IStatus returnstatus = Status.OK_STATUS;

		try {
			boolean retval;

			setTimeout();
			UltimateServices.getInstance().initializeResultMap();
			UltimateServices.getInstance().initializeTranslatorSequence();

			if ((mJobMode == ChainMode.RERUN_TOOLCHAIN || mJobMode == ChainMode.RUN_OLDTOOLCHAIN) && !mCore.canRerun()) {
				throw new Exception("Rerun called without previous run! Aborting...");
			}
			// all modes requires this
			mCore.resetCore();

			// only RUN_TOOLCHAIN and RUN_OLDTOOLCHAIN require this
			if (mJobMode == ChainMode.RUN_TOOLCHAIN || mJobMode == ChainMode.RUN_OLDTOOLCHAIN) {
				mCore.setInputFile(mInputFile);

			}

			// all but RERUN_TOOLCHAIN require this!
			if (mJobMode != ChainMode.RERUN_TOOLCHAIN) {
				retval = mCore.initiateParser(mPreludeFile);
				if (!retval) {
					throw new Exception();
				}

			}

			// only RUN_TOOLCHAIN and RUN_NEWTOOLCHAIN require this
			if (mJobMode == ChainMode.RUN_TOOLCHAIN || mJobMode == ChainMode.RUN_NEWTOOLCHAIN) {
				mChain = mCore.makeToolSelection();
				if (mChain == null) {
					mLogger.warn("Toolchain selection failed, aborting...");
					return new Status(Status.CANCEL, Activator.s_PLUGIN_ID, "Toolchain selection canceled");
				}
			}

			mCore.runParser();

			returnstatus = this.mCore.processToolchain(monitor);

		} catch (final Throwable e) {
			mLogger.fatal(String.format("The toolchain threw an exception: %s", e.getMessage()));
			mLogger.fatal(e);
			mController.displayException("The toolchain threw an exception", e);
			returnstatus = Status.CANCEL_STATUS;
			String idOfCore = Activator.s_PLUGIN_ID;
			UltimateServices.getInstance().reportResult(idOfCore, new ExceptionOrErrorResult(idOfCore, e));
		} finally {
			monitor.done();
			logResults();
		}

		return returnstatus;
	}

}
