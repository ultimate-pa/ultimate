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
 * @author dietsch
 * 
 */
public class DefaultToolchainJob extends BasicToolchainJob {

	private File mInputFile;
	private IToolchain mToolchain;

	/**
	 * Prepare to run a normal toolchain with this constructor.
	 * 
	 * @param name
	 *            The name of the job. Will be displayed in the UI.
	 * @param core
	 *            The currently active Ultimate Core.
	 * @param logger
	 *            The logger that is used to print information about the
	 *            toolchain execution.
	 * @param input
	 *            The files on which the toolchain should run.
	 * @param preludefile
	 *            A {@link PreludeProvider} describing the prelude the parser
	 *            should use.
	 */
	public DefaultToolchainJob(String name, ICore core, IController controller, Logger logger, File input,
			PreludeProvider preludefile) {
		super(name, core, controller, logger);
		setUser(true);
		setSystem(false);
		mInputFile = input;
		mPreludeFile = preludefile;
	}

	/**
	 * Prepare to rerun the given toolchain (if possible)
	 * 
	 * @param name
	 * @param core
	 * @param controller
	 * @param logger
	 * @param toolchain
	 */
	public DefaultToolchainJob(String name, ICore core, IController controller, Logger logger, IToolchain toolchain) {
		super(name, core, controller, logger);
		setUser(true);
		setSystem(false);
		setToolchain(toolchain);
		mJobMode = ChainMode.RERUN;
	}

	private void setToolchain(IToolchain toolchain) {
		assert toolchain != null;
		//TODO: Check if we can rerun the toolchain (but: why not?) 
		mToolchain = toolchain;
	}

	/**
	 * This method releases the active toolchain back to the core. Overwrite
	 * this method if you want to delay the release of the toolchain.
	 * 
	 * @param currentToolchain
	 */
	protected void releaseToolchain(IToolchain currentToolchain) {
		mCore.releaseToolchain(currentToolchain);
	}

	@Override
	protected IStatus runToolchainKeepToolchain(IProgressMonitor monitor) {
		throw new UnsupportedOperationException();
	}

	@Override
	protected IStatus runToolchainKeepInput(IProgressMonitor monitor) {
		throw new UnsupportedOperationException();
	}

	@Override
	protected IStatus rerunToolchain(IProgressMonitor monitor) {
		IStatus returnstatus = Status.OK_STATUS;
		monitor.beginTask(getName(), IProgressMonitor.UNKNOWN);

		try {
			//TODO: TC services need to be reseted ...
			mToolchain.init();
			monitor.worked(1);

			setServices(mToolchain.getCurrentToolchainData().getServices());
			monitor.worked(1);

			mToolchain.runParser();
			monitor.worked(1);

			returnstatus = mToolchain.processToolchain(monitor);

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
			releaseToolchain(mToolchain);
		}

		return returnstatus;
	}

	@Override
	protected IStatus runToolchainDefault(IProgressMonitor monitor) {
		IStatus returnstatus = Status.OK_STATUS;
		monitor.beginTask(getName(), IProgressMonitor.UNKNOWN);
		IToolchain currentToolchain = null;

		try {
			boolean retval;

			currentToolchain = mCore.requestToolchain();
			monitor.worked(1);

			currentToolchain.init();
			monitor.worked(1);

			currentToolchain.setInputFile(mInputFile);
			monitor.worked(1);

			retval = currentToolchain.initializeParser(mPreludeFile);
			if (!retval) {
				throw new Exception();
			}
			monitor.worked(1);

			mChain = currentToolchain.makeToolSelection();
			if (mChain == null) {
				mLogger.warn("Toolchain selection failed, aborting...");
				return new Status(Status.CANCEL, Activator.s_PLUGIN_ID, "Toolchain selection canceled");
			}
			setServices(mChain.getServices());
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
			releaseToolchain(currentToolchain);
		}

		return returnstatus;
	}

}
