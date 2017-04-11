package de.uni_freiburg.informatik.ultimate.interactive.conversion;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeRegistry;
import de.uni_freiburg.informatik.ultimate.interactive.utils.ToolchainStorageUtil;

/**
 * This class encapsulates type conversion for plugins that want to use the interactive interface. It should be
 * overridden in all type-converter plugins. Only a module responsible for setting up converted interfaces (the
 * Controller) will have to import the package. For plugins that want to use the interface, it suffices to import the
 * interactive package.
 * 
 * @author Julian Jarecki
 *
 * @param <A>
 * @param <B>
 */
public abstract class Converter<A, B> {
	private final ConverterRegistry<A, B> mConverterRegistry;
	private final Class<B> mTargetClass;
	private IInteractive<B> mTargetInterface;
	private final IUltimateServiceProvider mServices;

	protected Converter(IUltimateServiceProvider services, Class<B> targetClass) {
		mServices = services;
		mTargetClass = targetClass;
		mConverterRegistry = new ConverterRegistry<>();

		init(mConverterRegistry);
	}
	
	protected final IUltimateServiceProvider getServices() {
		return mServices;
	}

	protected abstract void init(final ConverterRegistry<A, B> converterRegistry);

	public static class Initializer<A> implements IStorable {
		private static final String STORAGE_IDENTIFIER_PREFIX = Initializer.class.getName();

		private static <M> String getStorageIdentifier(final Class<M> bound) {
			return STORAGE_IDENTIFIER_PREFIX + "_" + bound.getName();
		}

		private final IInteractive<A> mSourceInterface;
		private final ITypeRegistry<A> mTypeRegistry;

		public Initializer(IInteractive<A> sourceInterface, ITypeRegistry<A> typeRegistry) {
			super();
			this.mSourceInterface = sourceInterface;
			this.mTypeRegistry = typeRegistry;
		}

		public <B> IInteractive<B> getConvertedInteractiveInterface(final Converter<A, B> converter) {
			converter.mConverterRegistry.registerATypes(mTypeRegistry);
			return new ApplyConversionToInteractive<>(mSourceInterface, converter.mConverterRegistry,
					converter.mTargetClass);
		}

		public void store(final Class<A> typeBound, final IToolchainStorage storage) {
			storage.putStorable(getStorageIdentifier(typeBound), this);
		}

		@SuppressWarnings("unchecked")
		public static <A> Initializer<A> fromStorage(final Class<A> typeBound, final IToolchainStorage storage) {
			return (Initializer<A>) storage.getStorable(getStorageIdentifier(typeBound));
		}

		@Override
		public void destroy() {
		}
	}

	public IInteractive<B> getInterface() {
		return mTargetInterface;
	}
}
