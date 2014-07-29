package de.uni_freiburg.informatik.ultimate.core.services;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.IServiceFactoryFactory;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IServiceFactory;

public class GenericServiceProvider implements IStorable {

	private static final String sKey = "GenericServiceProvider";
	private final IServiceFactoryFactory mFactory;

	public GenericServiceProvider(IServiceFactoryFactory factory) {
		mFactory = factory;
	}

	@SuppressWarnings("unchecked")
	static <T extends IService> T getServiceInstance(
			ToolchainStorage toolchainStorage,
			Class<IServiceFactory<T>> serviceType) {
		assert toolchainStorage != null;

		// first, check if this instance already exists in storage
		IStorable storable = toolchainStorage
				.getStorable(serviceType.getName());
		if (storable != null) {
			return (T) storable;
		}

		// no it doesnt, we need to create a new one
		GenericServiceProvider instance = (GenericServiceProvider) toolchainStorage
				.getStorable(sKey);
		T rtrValue = instance.mFactory.createService(serviceType,
				toolchainStorage, toolchainStorage);
		toolchainStorage.putStorable(serviceType.getName(), rtrValue);
		return rtrValue;
	}

	public static String getServiceKey() {
		return sKey;
	}

	@Override
	public void destroy() {
		// doesnt need destruction, the actual services destroy themselves 
	}

}
