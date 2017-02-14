package de.uni_freiburg.informatik.ultimate.interactive.conversion;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeRegistry;
import de.uni_freiburg.informatik.ultimate.interactive.utils.ToolchainUtil;

/**
 * This class encapsulates type conversion for plugins that want to use the
 * interactive interface. It should be overridden in all type-converter plugins.
 * Only a module responsible for setting up converted interfaces (the
 * Controller) will have to import the package. For plugins that want to use the
 * interface, it suffices to import the interactive package.
 * 
 * @author Julian Jarecki
 *
 * @param <A>
 * @param <B>
 */
public abstract class Converter<A, B> {
	private final ConverterRegistry<A, B> mConverterRegistry;
	private final Class<B> mTargetClass;
	private final IToolchainStorage mStorage;
	private IInteractive<B> mTargetInterface;

	protected Converter(Class<B> targetClass, final IToolchainStorage storage) {
		mTargetClass = targetClass;
		mConverterRegistry = new ConverterRegistry<>();
		mStorage = storage;

		init(mConverterRegistry);
	}

	protected abstract void init(final ConverterRegistry<A, B> converterRegistry);

	public void initInterface(IInteractive<A> sourceInterface, ITypeRegistry<A> typeRegistry) {

		mConverterRegistry.registerATypes(typeRegistry);
		mTargetInterface = new ApplyConversionToInteractive<>(sourceInterface, mConverterRegistry, mTargetClass);
		if (mStorage != null)
			ToolchainUtil.storeInteractive(mTargetInterface, mTargetClass, mStorage);
	}

	public IInteractive<B> getInterface() {
		return mTargetInterface;
	}
}
