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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.observers;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.visitors.DebugRCFGVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker.ObserverDispatcher;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker.ObserverDispatcherSequential;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker.RCFGWalkerUnroller;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;

/**
 * 
 * @author dietsch
 * 
 */
public class DependencyFinder extends BaseObserver {

	private final int mUnrollings;
	private final ILogger mLogger;

	public DependencyFinder(ILogger logger) {
		super();
		mUnrollings = 1;
		mLogger = logger;
	}

	@Override
	public boolean process(IElement root) {

		// doit(root, mUnrollings);


		// for (int i = 1; i <= 3; ++i) {
		// doit(root, i);
		// }

		return false;
	}

	private void doit(IElement root, int unrollings) {
		final ObserverDispatcher od = new ObserverDispatcherSequential(mLogger);
		final RCFGWalkerUnroller walker = new RCFGWalkerUnroller(od, mLogger, unrollings);
		od.setWalker(walker);

		walker.addObserver(new DebugRCFGVisitor(mLogger, 500));
		// walker.addObserver(new UseDefVisitor());
		// walker.addObserver(new SequencingVisitor(walker));
		Collection<IcfgEdge> startEdges = BoogieIcfgContainer.extractStartEdges((BoogieIcfgContainer) root);
		walker.run(startEdges);

		final DebugFileWriterDietsch dfw = new DebugFileWriterDietsch(walker.getPaths(), mLogger, unrollings);
		dfw.run();
	}



}
