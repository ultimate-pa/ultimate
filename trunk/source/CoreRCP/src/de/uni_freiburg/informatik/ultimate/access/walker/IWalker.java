package de.uni_freiburg.informatik.ultimate.access.walker;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.model.IElement;


/**
 * 
 * This interface describes all Ultimate walkers. A walker is used to traverse a
 * graph in a given order. A connected observer can execute operations on every
 * node and every edge on the graph, given the model permits the operation
 * 
 * This interface belongs to the Ultimate access layer.
 *
 * 
 * @author dietsch
 * 
 */

public interface IWalker {
	
	public abstract boolean addObserver(IObserver observer);
	
	public abstract boolean removeObserver(IObserver observer);
	
	public abstract void removeAllObservers();
	
	public abstract boolean containsObserver(IObserver observer);
	
	public void run(IElement node);
}
