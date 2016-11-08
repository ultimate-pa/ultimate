/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class AbstractInterpretationRcfgObserver extends BaseObserver {
	
	private static final String ULTIMATE_START = "ULTIMATE.start";
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	
	public AbstractInterpretationRcfgObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}
	
	@Override
	public boolean process(final IElement elem) throws Throwable {
		if (!(elem instanceof BoogieIcfgContainer)) {
			throw new IllegalArgumentException("You cannot use this observer for " + elem.getClass().getSimpleName());
		}
		final BoogieIcfgContainer root = (BoogieIcfgContainer) elem;
		
		final List<CodeBlock> initial = getInitialEdges(root);
		if (initial == null) {
			throw new IllegalArgumentException("Could not find an initial edge");
		}
		
		final IPreferenceProvider ups = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final IProgressAwareTimer timer;
		if (ups.getBoolean(AbsIntPrefInitializer.LABEL_RUN_AS_PRE_ANALYSIS)) {
			timer = mServices.getProgressMonitorService().getChildTimer(0.2);
		} else {
			timer = mServices.getProgressMonitorService();
		}
		
		if (ups.getBoolean(AbsIntPrefInitializer.LABEL_USE_FUTURE_RCFG)) {
			AbstractInterpreter.runFuture(root, initial, timer, mServices, false);
		} else {
			AbstractInterpreter.run(root, initial, timer, mServices);
		}
		
		// do not descend, this is already the root
		return false;
	}
	
	private List<CodeBlock> getInitialEdges(final BoogieIcfgContainer root) {
		final Collection<IcfgEdge> startEdges = BoogieIcfgContainer.extractStartEdges(root);
		
		final Set<BoogieIcfgLocation> ultimateStartNodes = startEdges.stream().map(a -> a.getSource())
				.filter(source -> source instanceof BoogieIcfgLocation
						&& ((BoogieIcfgLocation) source).getProcedure().equals(ULTIMATE_START))
				.map(a -> (BoogieIcfgLocation) a).collect(Collectors.toSet());
		if (!ultimateStartNodes.isEmpty()) {
			mLogger.info("Found entry method " + ULTIMATE_START);
			return ultimateStartNodes.stream().flatMap(a -> a.getOutgoingEdges().stream()).map(a -> (CodeBlock) a)
					.collect(Collectors.toList());
		}
		mLogger.info("Did not find entry method " + ULTIMATE_START + ", using library mode");
		return startEdges.stream().filter(a -> a instanceof CodeBlock).map(a -> (CodeBlock) a)
				.collect(Collectors.toList());
	}
}
