package de.uni_freiburg.informatik.ultimate.interactive.traceabstraction;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.AbstractConverter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.TAConverterFactory;

public class ConverterFactory implements TAConverterFactory<GeneratedMessageV3> {

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
	public AbstractConverter<GeneratedMessageV3, Object> createConverter(final IUltimateServiceProvider services) {
		return new Converter(services);
	}

	@Override
	public Class<GeneratedMessageV3> sourceClass() {
		return GeneratedMessageV3.class;
	}

}