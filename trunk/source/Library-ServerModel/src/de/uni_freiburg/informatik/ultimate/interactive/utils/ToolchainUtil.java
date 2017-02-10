package de.uni_freiburg.informatik.ultimate.interactive.utils;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;

public class ToolchainUtil {
	// ITool tool
	@SuppressWarnings("unchecked")
	public static <M> IInteractive<M> getInteractive(final IToolchainStorage storage,
			final Class<IInteractive<M>> interactive) {
		return (IInteractive<M>) storage.getStorable(interactive.getName());
	}

	public static <M> void storeInteractive(IInteractive<M> interactive, final IToolchainStorage storage) {
		storage.putStorable(interactive.getClass().getName(), interactive);
	}
}
