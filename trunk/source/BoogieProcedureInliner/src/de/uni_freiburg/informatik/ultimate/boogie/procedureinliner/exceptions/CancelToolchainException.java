/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.exceptions;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.Activator;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AbstractResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * This exception indicates, that the toolchain should be canceled.
 * Use {@link #logErrorAndCancelToolchain(IUltimateServiceProvider, String)} to do so.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public abstract class CancelToolchainException extends Exception {

	private static final long serialVersionUID = -1545501978581884257L;

	private final ILocation mLocation;
	
	/**
	 * Creates a new Exception, indicating that the toolchain should be canceled.
	 * @param message Message to be logged to the logger.
	 * @param location Location inside the boogie program, where the exception arose.
	 * 				   Use null, if the location is unknown.
	 */
	public CancelToolchainException(String message, ILocation location) {
		super(message);
		mLocation = location;
	}

	public ILocation getLocation() {
		return mLocation;
	}

	public void logErrorAndCancelToolchain(IUltimateServiceProvider services, String pluginId) {
		final String logMessage = (mLocation == null ?  "" : mLocation + ": ") + getMessage();
		services.getLoggingService().getLogger(Activator.PLUGIN_ID).error(logMessage);
		services.getResultService().reportResult(pluginId, createResult(pluginId));
		services.getProgressMonitorService().cancelToolchain();
	}
	
	/**
	 * Creates a result to be reported to the Ultimate RResultService.
	 * @param pluginId Id of the plug-in.
	 * @return Result from the (canceled) toolchain.
	 */
	abstract protected AbstractResult createResult(String pluginId);
}
