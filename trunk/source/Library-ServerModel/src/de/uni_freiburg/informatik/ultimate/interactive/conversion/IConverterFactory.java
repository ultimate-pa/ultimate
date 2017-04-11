package de.uni_freiburg.informatik.ultimate.interactive.conversion;

import de.uni_freiburg.informatik.ultimate.core.model.IServiceFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;

public interface IConverterFactory<S, T> extends IServiceFactory<IInteractive<T>> {
	Converter<S, T> createConverter(IUltimateServiceProvider services);

	Class<S> sourceClass();

	@Override
	default IInteractive<T> createInstance(IUltimateServiceProvider services, IToolchainStorage storage) {
		Converter<S, T> converter = createConverter(services);

		final Converter.Initializer<S> initializer = Converter.Initializer.fromStorage(sourceClass(), storage);

		return initializer == null ? null : initializer.getConvertedInteractiveInterface(converter);
	}

}