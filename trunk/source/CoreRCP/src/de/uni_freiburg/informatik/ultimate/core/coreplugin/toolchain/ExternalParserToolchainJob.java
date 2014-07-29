package de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchain;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;

public class ExternalParserToolchainJob extends BasicToolchainJob {

	private IElement mAST;
	private GraphType mOutputDefinition;

	public ExternalParserToolchainJob(String name, ICore core, IController controller, IElement ast,
			GraphType outputDefinition, Logger logger) {
		super(name, core, controller, logger);
		mAST = ast;
		mOutputDefinition = outputDefinition;
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
		throw new UnsupportedOperationException();
	}

	@Override
	protected IStatus runToolchainDefault(IProgressMonitor monitor) {

		IStatus returnstatus = Status.OK_STATUS;
		monitor.beginTask(getName(), IProgressMonitor.UNKNOWN);
		IToolchain currentToolchain = null;

		try {
			monitor.worked(1);
			if ((mJobMode == ChainMode.RERUN || mJobMode == ChainMode.KEEP_Toolchain)) {
				throw new Exception("Rerun currently unsupported! Aborting...");
			}
			// all modes requires this
			currentToolchain = mCore.requestToolchain();

			currentToolchain.init();
			monitor.worked(1);
			// only RUN_TOOLCHAIN and RUN_NEWTOOLCHAIN require this

			if (mJobMode == ChainMode.DEFAULT || mJobMode == ChainMode.KEEP_INPUT) {
				mChain = currentToolchain.makeToolSelection();
				if (mChain == null) {
					mLogger.warn("Toolchain selection failed, aborting...");
					return new Status(Status.CANCEL, Activator.s_PLUGIN_ID, "Toolchain selection canceled");
				}
				setServices(mChain.getServices());
			}

			monitor.worked(1);
			currentToolchain.addAST(mAST, mOutputDefinition);
			monitor.worked(1);
			returnstatus = currentToolchain.processToolchain(monitor);

		} catch (final Throwable e) {
			mLogger.fatal(String.format("The toolchain threw an exception: %s", e.getMessage()));
			mLogger.fatal(e);
			mController.displayException("The toolchain threw an exception", e);
			returnstatus = Status.CANCEL_STATUS;
			String idOfCore = Activator.s_PLUGIN_ID;
			mServices.getResultService().reportResult(idOfCore, new ExceptionOrErrorResult(idOfCore, e));
		} finally {
			monitor.worked(1);
			logResults();
			mCore.releaseToolchain(currentToolchain);
			// TODO: Maybe we need to destroy the storage here, but I think not.
			monitor.done();
		}

		return returnstatus;
	}

}
