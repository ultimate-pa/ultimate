package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IServiceFactory;

public interface IServiceFactoryFactory {
	<T,K extends IServiceFactory<T>> T createService(Class<K> service,
			IUltimateServiceProvider services, IToolchainStorage storage);
}
