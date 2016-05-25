/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.core.coreplugin.modelwalker;

import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class BaseWalker implements IWalker {

	protected ILogger mLogger;
	protected List<IObserver> mObservers;

	protected BaseWalker(ILogger logger) {
		mObservers = new LinkedList<IObserver>();
		mLogger = logger;
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
	 * The walker will traverse the given subtree for each observer sequentially in the order of their insertion.
	 * 
	 * @param inode
	 *            usually the starting point
	 * @throws Throwable
	 *             iff an error occurs during plugin execution and the toolchain should be aborted.
	 */
	@Override
	public void run(IElement inode) throws Throwable {
		if (inode != null) {
			for (final IObserver v : mObservers) {
				runObserver(inode, v);
			}
		}
	}

	private void runObserver(IElement root, IObserver observer) throws Throwable {
		if (observer instanceof IUnmanagedObserver) {
			runObserver(root, (IUnmanagedObserver) observer);
		} else {
			mLogger.error("Illegal observer type supplied, aborting...");
		}
	}

	protected abstract void runObserver(IElement root, IUnmanagedObserver observer) throws Throwable;

}
