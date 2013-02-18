package local.stalin.access;

import local.stalin.model.INode;

/**
 * 
 * This interface describes all STALIN walkers. A walker is used to traverse a
 * graph in a given order. A connected observer can execute operations on every
 * node and every edge on the graph, given the model permits the operation
 * 
 * This interface belongs to the STALIN access layer.
 *
 * This interface is under construction and subject to change. 
 * 
 * @author dietsch
 * 
 */

public interface IWalker {
	
	public abstract boolean addObserver(IObserver observer);
	
	public abstract boolean removeObserver(IObserver observer);
	
	public abstract void removeAllObservers();
	
	public abstract boolean containsObserver(IObserver observer);
	
	public void run(INode node);
}
