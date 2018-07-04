/*
 * Copyright (C) 2010-2015 Christian Simon
 * Copyright (C) 2012-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain;

import java.io.File;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.RcpProgressMonitorWrapper;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.ParserInitializationException;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainProgressMonitor;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * This class implements an Eclipse Job processing a Ultimate toolchain using the methods publicly available from ICore
 * <ToolchainListType>.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class DefaultToolchainJob extends BasicToolchainJob {

	protected File[] mInputFiles;
	protected IToolchain<RunDefinition> mToolchain;

	/**
	 * Use this constructor to run a new toolchain
	 *
	 * @param name
	 *            The name of the job. Will be displayed in the UI.
	 * @param core
	 *            The currently active Ultimate Core.
	 * @param logger
	 *            The logger that is used to print information about the toolchain execution.
	 * @param input
	 *            The files on which the toolchain should run.
	 */
	public DefaultToolchainJob(final String name, final ICore<RunDefinition> core,
			final IController<RunDefinition> controller, final ILogger logger, final File[] input) {
		super(name, core, controller, logger);
		setUser(true);
		setSystem(false);
		if (input == null || input.length == 0) {
			throw new IllegalArgumentException("No input files given");
		}
		mInputFiles = input;
	}

	/**
	 * Use this constructor to re-run the given toolchain.
	 *
	 * @param name
	 * @param core
	 * @param controller
	 * @param logger
	 * @param toolchain
	 */
	public DefaultToolchainJob(final String name, final ICore<RunDefinition> core,
			final IController<RunDefinition> controller, final ILogger logger,
			final IToolchain<RunDefinition> toolchain) {
		super(name, core, controller, logger);
		setUser(true);
		setSystem(false);
		setToolchain(toolchain);
	}

	protected void setToolchain(final IToolchain<RunDefinition> toolchain) {
		assert toolchain != null;
		mToolchain = toolchain;
	}

	/**
	 * This method releases the active toolchain back to the core. Overwrite this method if you want to delay the
	 * release of the toolchain.
	 *
	 * @param currentToolchain
	 */
	protected void releaseToolchain() {
		mCore.releaseToolchain(mToolchain);
	}

	@Override
	protected IStatus run(final IProgressMonitor monitor) {
		final IToolchainProgressMonitor tpm = RcpProgressMonitorWrapper.create(monitor);
		tpm.beginTask(getName(), IProgressMonitor.UNKNOWN);

		try {
			setToolchain(mCore.requestToolchain(mInputFiles));
			tpm.worked(1);

			mToolchain.init(tpm);
			tpm.worked(1);

			if (!mToolchain.initializeParsers()) {
				throw new ParserInitializationException();
			}
			tpm.worked(1);

			final IToolchainData<RunDefinition> chain = mToolchain.makeToolSelection(tpm);
			if (chain == null) {
				mLogger.fatal("Toolchain selection failed, aborting...");
				return new Status(IStatus.CANCEL, Activator.PLUGIN_ID, IStatus.CANCEL, "Toolchain selection canceled",
						null);
			}
			setServices(chain.getServices());
			tpm.worked(1);

			mToolchain.runParsers();
			tpm.worked(1);

			return convert(mToolchain.processToolchain(tpm));
		} catch (final Throwable e) {
			return handleException(e);
		} finally {
			tpm.done();
			releaseToolchain();
		}
	}

	protected IStatus handleException(final Throwable e) {
		if (e == null) {
			mLogger.fatal("The toolchain wants to handle an exception, but provided nothing");
		} else if (mLogger.isDebugEnabled()) {
			mLogger.fatal("The toolchain threw an exception", e);
		} else {
			mLogger.fatal(String.format("The toolchain threw an exception: %s: %s", e.getClass(), e.getMessage()));
		}
		mController.displayException(mToolchain.getCurrentToolchainData(), "The toolchain threw an exception", e);
		if (mServices != null) {
			final String idOfCore = Activator.PLUGIN_ID;
			mServices.getResultService().reportResult(idOfCore, new ExceptionOrErrorResult(idOfCore, e));
		}
		return new Status(IStatus.ERROR, Activator.PLUGIN_ID, IStatus.ERROR, "Toolchain threw an exception", null);
	}

}
