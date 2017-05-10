package de.uni_freiburg.informatik.ultimate.interactive.utils;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;

public class ToolchainStorageUtil {
	private static final String STORAGE_IDENTIFIER_PREFIX = IInteractive.class.getName();

	private static <M> String getStorageIdentifier(final Class<M> bound) {
		return STORAGE_IDENTIFIER_PREFIX + "_" + bound.getName();
	}

	// ITool tool
	@SuppressWarnings("unchecked")
	public static <M> IInteractive<M> getInteractive(final IToolchainStorage storage, final Class<M> bound) {
		return (IInteractive<M>) storage.getStorable(getStorageIdentifier(bound));
	}

	public static <M> void storeInteractive(final IInteractive<M> interactive, final Class<M> bound,
			final IToolchainStorage storage) {
		storage.putStorable(getStorageIdentifier(bound), interactive);
	}
}
