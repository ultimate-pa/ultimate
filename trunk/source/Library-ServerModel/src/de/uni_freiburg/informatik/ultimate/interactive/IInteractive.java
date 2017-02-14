package de.uni_freiburg.informatik.ultimate.interactive;

import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.interactive.utils.ToolchainUtil;

/**
 * Interface that provides a way to communicate directly with Clients
 * asynchronously in a type-safe manner.
 * 
 * If a Toolchain Plugin wants to use the interface, it suffices to import this
 * Interface.
 * 
 * @author Julian Jarecki
 *
 * @param <M>
 */
public interface IInteractive<M> extends IHandlerRegistry<M>, IInteractiveQueue<M>, IStorable {
	@Override
	default void destroy() {
		// The destroy method will usually not be needed for the Interactive
		// interface.
	}

	static <M> IInteractive<M> getFromStorage(final IToolchainStorage storage, final Class<M> typeBound) {
		return ToolchainUtil.getInteractive(storage, typeBound);
	}
}
