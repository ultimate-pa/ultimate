package de.uni_freiburg.informatik.ultimate.web.backend.util;

import java.io.IOException;
import java.util.List;
import java.util.concurrent.CountDownLatch;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.RcpProgressMonitorWrapper;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.ParserInitializationException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain.ReturnCode;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainProgressMonitor;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.web.backend.dto.ToolchainResponse;
import de.uni_freiburg.informatik.ultimate.web.backend.dto.UltimateResult;

public class WebBackendToolchainJob extends DefaultToolchainJob {

	private final ILogger mServletLogger;
	private final String mId;

	public WebBackendToolchainJob(final String name, final ICore<RunDefinition> core,
			final IController<RunDefinition> controller, final ILogger logger,
			final IToolchain<RunDefinition> toolchain, final String id) {
		super(name, core, controller, logger, toolchain);
		mServletLogger = logger;
		mId = id;
	}

	@Override
	protected IStatus run(final IProgressMonitor monitor) {
		final IToolchainProgressMonitor tpm = RcpProgressMonitorWrapper.create(monitor);
		tpm.beginTask(getName(), IProgressMonitor.UNKNOWN);

		try {
			tpm.worked(1);

			mToolchain.init(tpm);
			tpm.worked(1);

			if (!mToolchain.initializeParsers()) {
				throw new ParserInitializationException();
			}
			tpm.worked(1);

			final IToolchainData<RunDefinition> chain = mToolchain.makeToolSelection(tpm);
			if (chain == null) {
				mServletLogger.fatal("Toolchain selection failed, aborting...");
				return new Status(IStatus.CANCEL, Activator.PLUGIN_ID, IStatus.CANCEL, "Toolchain selection canceled",
						null);
			}
			setServices(chain.getServices());
			tpm.worked(1);

			mToolchain.runParsers();
			tpm.worked(1);

			final ReturnCode tcReturnCode = mToolchain.processToolchain(tpm);
			storeToolchainResult(tcReturnCode, null);
			return convert(tcReturnCode);
		} catch (final Throwable e) {
			mServletLogger.error("Error running the Toolchain: " + e.getMessage());
			storeToolchainResult(ReturnCode.Error, e);
			return handleException(e);
		} finally {
			tpm.done();
			releaseToolchain();
		}
	}

	private void storeToolchainResult(final ReturnCode result, final Throwable e) {
		final ToolchainResponse tcResponse = new ToolchainResponse(getId());
		final IUltimateServiceProvider tcServices = mToolchain.getCurrentToolchainData().getServices();
		final List<UltimateResult> results = UltimateResultConverter.processUltimateResults(mServletLogger, tcServices);
		if (e != null && tcServices.getResultService().getResults().entrySet().stream()
				.noneMatch(a -> a.getValue().stream().anyMatch(ExceptionOrErrorResult.class::isInstance))) {
			results.add(UltimateResultConverter.processResult(mServletLogger,
					new ExceptionOrErrorResult(Activator.PLUGIN_ID, e)));
		}
		tcResponse.setResults(results);
		switch (result) {
		case Ok:
		case Cancel:
		case Error:
			// every exit of Ultimate is ok from the POV of the WebBackend
			tcResponse.setStatus("done");
			break;
		default:
			tcResponse.setStatusError();
			mServletLogger.error("Unknown return code %s", result);
			break;
		}

		try {
			tcResponse.store(mServletLogger);
		} catch (final IOException ex) {
			mServletLogger.error("Could not store toolchain result", ex);
		}
	}

	@Override
	public boolean belongsTo(final Object family) {
		return family == "WebBackendToolchainJob";
	}

	public String getId() {
		return mId;
	}

	public CountDownLatch cancelToolchain() {
		return mServices.getProgressMonitorService().cancelToolchain();
	}

}
