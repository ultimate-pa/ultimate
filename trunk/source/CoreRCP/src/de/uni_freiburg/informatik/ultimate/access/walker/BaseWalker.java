package de.uni_freiburg.informatik.ultimate.access.walker;

import java.util.LinkedList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IManagedObserver;
import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.model.IElement;

public abstract class BaseWalker implements IWalker {

	protected static Logger sLogger = UltimateServices.getInstance().getLogger(
			Activator.s_PLUGIN_ID);
	protected List<IObserver> mObservers;

	protected BaseWalker() {
		mObservers = new LinkedList<IObserver>();

	}

	@Override
	public boolean addObserver(IObserver v) {
		return mObservers.add(v);
	}

	@Override
	public boolean removeObserver(IObserver observer) {
		return mObservers.remove(observer);
	}

	@Override
	public void removeAllObservers() {
		mObservers.clear();

	}

	@Override
	public boolean containsObserver(IObserver observer) {
		return mObservers.contains(observer);
	}
	
	/**
	 * The walker will traverse the given subtree for each observer sequentially
	 * in the order of their insertion.
	 * 
	 * @param inode
	 *            usually the starting point
	 * @throws Throwable iff an error occurs during plugin execution and the toolchain should be aborted. 
	 */
	public void run(IElement inode) throws Throwable {
		if (inode != null) {
			for (IObserver v : mObservers) {
				runObserver(inode, v);
			}
		}
	}

	private void runObserver(IElement root, IObserver observer) throws Throwable {
		if (observer instanceof IUnmanagedObserver) {
			runObserver(root, (IUnmanagedObserver) observer);
		} else if (observer instanceof IManagedObserver) {
			runObserver(root, (IManagedObserver) observer);
		} else {
			sLogger.error("Illegal observer type supplied, aborting...");
		}
	}
	
	protected abstract void runObserver(IElement root, IUnmanagedObserver observer) throws Throwable;
	protected abstract void runObserver(IElement root, IManagedObserver observer);

}
