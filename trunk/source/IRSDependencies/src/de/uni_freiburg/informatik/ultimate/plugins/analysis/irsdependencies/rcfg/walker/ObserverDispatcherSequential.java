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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.visitors.SimpleRCFGVisitor;

public class ObserverDispatcherSequential extends ObserverDispatcher
{

	public ObserverDispatcherSequential(ILogger logger) {
		super(logger);
	}

	private SimpleRCFGVisitor mCurrentVisitor;

	@Override
	public void run(final Collection<IcfgEdge> startEdges)
	{

		for (final SimpleRCFGVisitor visitor : mObservers) {
			mCurrentVisitor = visitor;
			mCurrentVisitor.init(null, 0, 1);
			mWalker.startFrom(startEdges);
			mCurrentVisitor.finish();
		}

	}

	@Override
	protected void callObservers(IRCFGVisitorDispatcher dispatcher)
	{
		dispatcher.dispatch(mCurrentVisitor);
	}

	@Override
	public boolean abortCurrentBranch()
	{
		return mCurrentVisitor.abortCurrentBranch();
	}
	
	@Override
	public boolean abortAll()
	{
		return mCurrentVisitor.abortAll();
	}
}
