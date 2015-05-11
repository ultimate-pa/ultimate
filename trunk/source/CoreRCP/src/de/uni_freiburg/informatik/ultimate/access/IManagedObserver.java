package de.uni_freiburg.informatik.ultimate.access;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

/**
 * @author dietsch
 *
 */
public interface IManagedObserver extends IObserver {

	WalkerOptions.Command[] process(IPayload payload, WalkerOptions.State state, int childCount);

}
