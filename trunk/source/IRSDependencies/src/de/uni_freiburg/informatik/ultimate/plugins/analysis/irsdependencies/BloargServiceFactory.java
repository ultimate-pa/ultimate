package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

public class BloargServiceFactory implements IBloargServiceFactory {

	@Override
	public String getPluginName() {
		return "Huar";
	}

	@Override
	public String getPluginID() {
		return "Hoehoehoe";
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		// no preferences
		return null;
	}

	@Override
	public BloargService createInstance(final IUltimateServiceProvider services, final IToolchainStorage storage) {
		final String key = BloargService.class.getName();
		final IStorable bloargService = storage.getStorable(key);
		if (bloargService instanceof BloargService) {
			return (BloargService) bloargService;
		}
		final BloargService newService = new BloargService();
		storage.putStorable(key, newService);
		return newService;
	}

	public static final class BloargService implements IService {

		@Override
		public void destroy() {
			// do nothing
		}

		public String iAmBloarg() {
			return "Bloarg";
		}

	}
}
