/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchain;
import de.uni_freiburg.informatik.ultimate.model.ModelType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;

public class ExternalParserToolchainJob extends BasicToolchainJob {

	private IElement mAST;
	private ModelType mOutputDefinition;

	public ExternalParserToolchainJob(String name, ICore core, IController controller, IElement ast,
			ModelType outputDefinition, Logger logger) {
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

			currentToolchain.init(monitor);
			monitor.worked(1);
			// only RUN_TOOLCHAIN and RUN_NEWTOOLCHAIN require this

			if (mJobMode == ChainMode.DEFAULT || mJobMode == ChainMode.KEEP_INPUT) {
				mChain = currentToolchain.makeToolSelection(monitor);
				if (mChain == null) {
					mLogger.warn("Toolchain selection failed, aborting...");
					return new Status(Status.CANCEL, Activator.PLUGIN_ID, "Toolchain selection canceled");
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
			String idOfCore = Activator.PLUGIN_ID;
			mServices.getResultService().reportResult(idOfCore, new ExceptionOrErrorResult(idOfCore, e));
		} finally {
			monitor.worked(1);
			logResults();
			releaseToolchain(currentToolchain);
			// TODO: Maybe we need to destroy the storage here, but I think not.
			monitor.done();
		}

		return returnstatus;
	}
	
	/**
	 * This method releases the active toolchain back to the core. Overwrite
	 * this method if you want to delay the release of the toolchain.
	 * 
	 * @param currentToolchain
	 */
	protected void releaseToolchain(IToolchain chain) {
		mCore.releaseToolchain(chain);
	}

}
