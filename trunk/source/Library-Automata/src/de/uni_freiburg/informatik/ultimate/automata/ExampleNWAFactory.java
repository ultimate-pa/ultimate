package de.uni_freiburg.informatik.ultimate.automata;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IServiceFactory;

public class ExampleNWAFactory implements IServiceFactory<NestedWordAutomata> {

	@Override
	public NestedWordAutomata createInstance(IUltimateServiceProvider services,
			IToolchainStorage storage) {
		NestedWordAutomata rtr = new NestedWordAutomata();
		rtr.setToolchainStorage(storage);
		rtr.setServices(services);
		rtr.init();
		return rtr;
	}

	@Override
	public String getPluginName() {
		return "Library-NestedWordAutomata";
	}

	@Override
	public String getPluginID() {
		return getClass().getPackage().getName();
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return null;
	}

}
