package de.uni_freiburg.informatik.ultimate.interactive;

import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;

/**
 * Interface that provides a way to communicate directly with Clients
 * asynchronously in a type-safe manner.
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
}
