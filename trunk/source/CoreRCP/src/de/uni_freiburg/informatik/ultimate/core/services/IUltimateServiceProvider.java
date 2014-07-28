package de.uni_freiburg.informatik.ultimate.core.services;

/**
 * 
 * @author dietsch
 *
 */
public interface IUltimateServiceProvider {

	IBacktranslationService getBacktranslationService();
	
	ILoggingService getLoggingService();
	
	IResultService getResultService();
	
	IProgressMonitorService getProgressMonitorService();
	
}
