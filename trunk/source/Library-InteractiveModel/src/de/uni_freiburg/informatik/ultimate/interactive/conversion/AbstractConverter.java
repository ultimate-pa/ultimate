package de.uni_freiburg.informatik.ultimate.interactive.conversion;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeRegistry;

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
public abstract class AbstractConverter<A, B> {
	private final ConverterRegistry<A, B> mConverterRegistry;
	private final Class<B> mTargetClass;
	private IInteractive<B> mTargetInterface;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	protected AbstractConverter(final ILogger logger, final Class<B> targetClass) {
		this(null, logger, targetClass);
	}

	protected AbstractConverter(final IUltimateServiceProvider services, final Class<B> targetClass) {
		// it would be nicer, if this could be identified with the class of the converted object
		this(services, services.getLoggingService().getLogger(AbstractConverter.class), targetClass);
	}

	private AbstractConverter(final IUltimateServiceProvider services, final ILogger logger, final Class<B> targetClass) {
		mServices = services;
		mLogger = logger;
		mTargetClass = targetClass;
		mConverterRegistry = new ConverterRegistry<>();

		init(mConverterRegistry);
	}

	protected final ILogger getLogger() {
		return mLogger;
	}
	
	protected final IUltimateServiceProvider getServices() {
		return mServices;
	}
	
	public final IInteractive<B> getInterface() {
		return mTargetInterface;
	}

	protected abstract void init(ConverterRegistry<A, B> converterRegistry);

	public static class Initializer<A> implements IStorable {
		private static final String STORAGE_IDENTIFIER_PREFIX = Initializer.class.getName();

		private final IInteractive<A> mSourceInterface;
		private final ITypeRegistry<A> mTypeRegistry;

		private static <M> String getStorageIdentifier(final Class<M> bound) {
			return STORAGE_IDENTIFIER_PREFIX + "_" + bound.getName();
		}

		public Initializer(final IInteractive<A> sourceInterface, final ITypeRegistry<A> typeRegistry) {
			super();
			this.mSourceInterface = sourceInterface;
			this.mTypeRegistry = typeRegistry;
		}

		public <B> IInteractive<B> getConvertedInteractiveInterface(final AbstractConverter<A, B> converter) {
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
			// nothing to be done here.
		}
	}
}
