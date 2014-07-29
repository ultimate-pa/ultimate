package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

public interface IServiceFactory<T> extends IUltimatePlugin {

	T createInstance(IUltimateServiceProvider services,
			IToolchainStorage storage);

}
