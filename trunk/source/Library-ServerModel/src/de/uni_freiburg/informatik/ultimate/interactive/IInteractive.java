package de.uni_freiburg.informatik.ultimate.interactive;

/**
 * Interface that provides a way to communicate directly with
 * Clients asynchronously in a type-safe manner.
 * 
 * @author Julian Jarecki
 *
 * @param <M>
 */
public interface IInteractive<M> extends IHandlerRegistry<M>, IInteractiveQueue<M> {
}
