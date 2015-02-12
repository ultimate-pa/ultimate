package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.AbstractResult;

/**
 * This exception indicates, that the toolchain should be canceled.
 * Use {@link #logErrorAndCancelToolchain(IUltimateServiceProvider, String)} to do so.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public abstract class CancelToolchainException extends Exception {

	private static final long serialVersionUID = -1545501978581884257L;

	private ILocation mLocation;
	
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
		String logMessage = (mLocation == null ?  "" : mLocation + ": ") + getMessage();
		services.getLoggingService().getLogger(logMessage);
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
