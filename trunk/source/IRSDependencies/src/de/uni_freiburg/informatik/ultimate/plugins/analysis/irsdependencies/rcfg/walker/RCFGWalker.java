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

import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.visitors.SimpleRCFGVisitor;

/**
 * The abstract class RCFGWalker provides standard observer handling (add,
 * remove, removeAll, contains) for all traversals of RCFG graphs. Basic usage
 * is as follows:
 * 
 * Create object with desired ObserverDispatcher.
 * 
 * Attach desired observers.
 * 
 * Call "run" on RCFG.
 * 
 * As walkers are responsible for the traversal, they normally contain the
 * algorithm necessary for searches and heuristics. The actual work is then done
 * by observers.
 * 
 * Please note that if you do not attach a observer to a walker, the dispatcher
 * will prevent executing the walking code.
 * 
 * @author dietsch
 * 
 */
public abstract class RCFGWalker implements IRCFGWalker {

	protected ObserverDispatcher mDispatcher;
	protected final ILogger mLogger;

	public RCFGWalker(ObserverDispatcher dispatcher, ILogger logger) {
		mDispatcher = dispatcher;
		mLogger = logger;
	}

	@Override
	public boolean addObserver(IObserver observer) {
		return mDispatcher.addObserver(observer);
	}

	@Override
	public boolean removeObserver(IObserver observer) {
		return mDispatcher.removeObserver(observer);
	}

	@Override
	public void removeAllObservers() {
		mDispatcher.removeAllObservers();
	}

	@Override
	public boolean containsObserver(IObserver observer) {
		return mDispatcher.containsObserver(observer);
	}

	@Override
	public void run(final Collection<IcfgEdge> startEdges) {
		mDispatcher.run(startEdges);
	}

	protected void programExitReached() {
		mDispatcher.callObservers(new IRCFGVisitorDispatcher() {
			@Override
			public void dispatch(SimpleRCFGVisitor visitor) {
				visitor.endOfTrace();
			}
		});
	}

	protected void pre(final IcfgLocation node) {
		mDispatcher.callObservers(new IRCFGVisitorDispatcher() {
			@Override
			public void dispatch(SimpleRCFGVisitor visitor) {
				visitor.pre(node);
			}
		});
	}

	protected void pre(final IcfgEdge edge) {
		mDispatcher.callObservers(new IRCFGVisitorDispatcher() {
			@Override
			public void dispatch(SimpleRCFGVisitor visitor) {
				visitor.pre(edge);
			}
		});
	}

	protected void post(final IcfgLocation node) {
		mDispatcher.callObservers(new IRCFGVisitorDispatcher() {
			@Override
			public void dispatch(SimpleRCFGVisitor visitor) {
				visitor.post(node);
			}
		});
	}

	protected void post(final IcfgEdge edge) {
		mDispatcher.callObservers(new IRCFGVisitorDispatcher() {
			@Override
			public void dispatch(SimpleRCFGVisitor visitor) {
				visitor.post(edge);
			}
		});
	}

	protected void level(final IcfgLocation node) {
		mDispatcher.callObservers(new IRCFGVisitorDispatcher() {
			@Override
			public void dispatch(SimpleRCFGVisitor visitor) {
				visitor.level(node);
			}
		});
	}

	protected void level(final IcfgEdge edge) {
		mDispatcher.callObservers(new IRCFGVisitorDispatcher() {
			@Override
			public void dispatch(SimpleRCFGVisitor visitor) {
				visitor.level(edge);
			}
		});
	}
}
