package de.uni_freiburg.informatik.ultimate.interactive.traceabstraction;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.model.IServiceFactory;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.Converter;

public class ConverterFactory implements IServiceFactory<IInteractive<Object>> {

	@Override
	public String getPluginName() {
		return "TAConverter";
	}

	@Override
	public String getPluginID() {
		return null;
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}

	@Override
	public IInteractive<Object> createInstance(IUltimateServiceProvider services, IToolchainStorage storage) {
		TAConverter converter = new TAConverter();

		System.out.println("test test test test test test test test test test test test test test test test !!!");

		final Converter.Initializer<GeneratedMessageV3> initializer =
				Converter.Initializer.fromStorage(GeneratedMessageV3.class, storage);

		return initializer == null ? null : initializer.getConvertedInteractiveInterface(converter);
	}

}