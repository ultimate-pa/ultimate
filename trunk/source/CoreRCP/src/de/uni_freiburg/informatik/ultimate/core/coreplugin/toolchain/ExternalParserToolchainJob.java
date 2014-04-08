package de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;

public class ExternalParserToolchainJob extends BasicToolchainJob {

	private IElement mAST;
	private GraphType mOutputDefinition;

	public ExternalParserToolchainJob(String name, ICore core, IController controller, ChainMode mode, IElement ast,
			GraphType outputDefinition) {
		super(name, core, controller, mode);
		mAST = ast;
		mOutputDefinition = outputDefinition;
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {

		IStatus returnstatus = Status.OK_STATUS;

		try {
			setTimeout();
			UltimateServices.getInstance().initializeResultMap();
			UltimateServices.getInstance().initializeTranslatorSequence();

			if ((mJobMode == ChainMode.RERUN_TOOLCHAIN || mJobMode == ChainMode.RUN_OLDTOOLCHAIN) && !mCore.canRerun()) {
				throw new Exception("Rerun called without previous run! Aborting...");
			}
			// all modes requires this
			mCore.resetCore();

			// only RUN_TOOLCHAIN and RUN_NEWTOOLCHAIN require this
			if (mJobMode == ChainMode.RUN_TOOLCHAIN || mJobMode == ChainMode.RUN_NEWTOOLCHAIN) {
				mChain = mCore.makeToolSelection();
				if (mChain == null) {
					mLogger.warn("Toolchain selection failed, aborting...");
					return new Status(Status.CANCEL, Activator.s_PLUGIN_ID, "Toolchain selection canceled");
				}
			}

			mCore.addAST(mAST, mOutputDefinition);

			returnstatus = mCore.processToolchain(monitor);

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
