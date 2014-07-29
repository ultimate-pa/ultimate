package de.uni_freiburg.informatik.ultimate.core.services;

import de.uni_freiburg.informatik.ultimate.ep.interfaces.IServiceFactory;

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

	<T extends IService> T getServiceInstance(Class<IServiceFactory<T>> serviceType);

}
