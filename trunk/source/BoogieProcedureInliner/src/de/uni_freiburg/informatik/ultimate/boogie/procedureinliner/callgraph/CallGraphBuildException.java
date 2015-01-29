package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.AbstractResult;

public abstract class CallGraphBuildException extends Exception {

	private static final long serialVersionUID = -1816806349288815778L;

	private Procedure mProcedure;
	
	public CallGraphBuildException(String message, Procedure procedure) {
		super(message);
		mProcedure = procedure;
	}

	public Procedure getProcedure() {
		return mProcedure;
	}
	
	public ILocation getLocation() {
		return mProcedure.getLocation();
	}
	
	public void logErrorAndCancelToolchain(IUltimateServiceProvider services, String pluginId) {
		services.getLoggingService().getLogger(pluginId).error(getLocation()+ ": " + getMessage());
		services.getResultService().reportResult(pluginId, createResult(pluginId));
		services.getProgressMonitorService().cancelToolchain();
	}
	
	abstract protected AbstractResult createResult(String pluginId);
}
