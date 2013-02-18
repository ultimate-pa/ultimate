package local.stalin.access;

import local.stalin.model.IPayload;

/**
 * This class
 * 
 * @author dietsch
 *
 */
public interface IManagedObserver extends IObserver{

	public abstract WalkerOptions.Command[] process(IPayload payload, WalkerOptions.State state, int childCount);
	
}
