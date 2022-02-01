/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.visitors.SimpleRCFGVisitor;

/**
 * 
 * ObserverDispatcher provides a flexible way to combine a certain way of graph
 * traversal (in,pre,postorder, breadth-first) with a certain order of observer
 * execution (either for each observer a own traversal, or in each node all
 * observers are called one after another).
 * 
 * This class and its descendants should only be used in conjunction with RCFGWalker
 * 
 * @author dietsch
 * 
 */
public abstract class ObserverDispatcher {
	protected List<SimpleRCFGVisitor> mObservers;
	
	protected final ILogger mLogger ;
	protected IRCFGWalker mWalker;

	public ObserverDispatcher(ILogger logger) {
		mObservers = new LinkedList<>();
		mLogger = logger;
	}

	public void setWalker(IRCFGWalker walker) {
		mWalker = walker;
	}

	public boolean addObserver(IObserver observer) {
		if (!(observer instanceof SimpleRCFGVisitor)) {
			mLogger.error("RCFGWalker only accepts RCFGVisitors");
			return false;
		}
		return mObservers.add((SimpleRCFGVisitor) observer);
	}

	public boolean removeObserver(IObserver observer) {
		return mObservers.remove(observer);
	}

	public void removeAllObservers() {
		mObservers.clear();
	}

	public boolean containsObserver(IObserver observer) {
		return mObservers.contains(observer);
	}

	public abstract void run(Collection<IcfgEdge> startEdges);

	protected abstract void callObservers(IRCFGVisitorDispatcher dispatcher);

	public abstract boolean abortCurrentBranch();

	public abstract boolean abortAll();

}
