package de.uni_freiburg.informatik.ultimate.access;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

/**
 * This class
 * 
 * @author dietsch
 *
 */
public interface IManagedObserver extends IObserver{

	public abstract WalkerOptions.Command[] process(IPayload payload, WalkerOptions.State state, int childCount);
	
}
