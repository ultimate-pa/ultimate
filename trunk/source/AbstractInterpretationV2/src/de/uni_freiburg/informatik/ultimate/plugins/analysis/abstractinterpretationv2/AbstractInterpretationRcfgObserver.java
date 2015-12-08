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

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbstractInterpretationPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class AbstractInterpretationRcfgObserver extends BaseObserver {

	private static final String ULTIMATE_START = "ULTIMATE.start";
	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;

	public AbstractInterpretationRcfgObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean process(IElement elem) throws Throwable {
		if (!(elem instanceof RootNode)) {
			throw new IllegalArgumentException("You cannot use this observer for " + elem.getClass().getSimpleName());
		}
		final RootNode root = (RootNode) elem;

		final List<CodeBlock> initial = getInitialEdges(root);
		if (initial == null) {
			throw new IllegalArgumentException("Could not find an initial edge");
		}

		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		final IProgressAwareTimer timer;
		if (ups.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_RUN_AS_PRE_ANALYSIS)) {
			timer = mServices.getProgressMonitorService().getChildTimer(0.2);
		} else {
			timer = mServices.getProgressMonitorService();
		}

		final Map<CodeBlock, Map<ProgramPoint, Term>> preds = AbstractInterpreter.run(root, initial, timer, mServices);
//		dumpToFile(preds);
		
		// do not descend, this is already the root
		return false;
	}

	private void dumpToFile(Map<CodeBlock, Map<ProgramPoint, Term>> preds) {
		StringBuilder sb = new StringBuilder();

		for (Entry<CodeBlock, Map<ProgramPoint, Term>> entry : preds.entrySet()) {
			if (entry.getValue().isEmpty()) {
				continue;
			}
			sb.append(entry.getKey().toString()).append("\n");
			for (Entry<ProgramPoint, Term> runPreds : entry.getValue().entrySet()) {
				sb.append(" * ").append(runPreds.getValue()).append("\n");
			}
		}
		if(sb.length() == 0){
			sb.append("No preds :(\n");
		}
		
		String filePath = "F:/repos/ultimate/trunk/source/UltimateTest/target/surefire-reports/de.uni_freiburg.informatik.ultimatetest.suites.evals.AbstractInterpretationMk2TestSuite/preds.txt";
		sb.append("\n\n");
		try {
			BufferedWriter bw = new BufferedWriter(new FileWriter(filePath,true));
			bw.append(sb);
			bw.close();
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	private List<CodeBlock> getInitialEdges(final RootNode root) {
		for (final RCFGEdge initialEdge : root.getOutgoingEdges()) {
			final ProgramPoint initialNode = (ProgramPoint) initialEdge.getTarget();
			if (initialNode.getProcedure().equals(ULTIMATE_START)) {
				final List<RCFGEdge> edges = initialNode.getOutgoingEdges();
				final List<CodeBlock> codeblocks = new ArrayList<CodeBlock>(edges.size());
				for (final RCFGEdge edge : edges) {
					codeblocks.add((CodeBlock) edge);
				}
				mLogger.info("Found entry method " + ULTIMATE_START);
				return codeblocks;
			}
		}
		mLogger.info("Did not find entry method " + ULTIMATE_START + ", using library mode");
		final List<CodeBlock> codeblocks = new ArrayList<CodeBlock>();
		for (final RCFGEdge initialEdge : root.getOutgoingEdges()) {
			final ProgramPoint initialNode = (ProgramPoint) initialEdge.getTarget();
			final List<RCFGEdge> edges = initialNode.getOutgoingEdges();
			for (final RCFGEdge edge : edges) {
				codeblocks.add((CodeBlock) edge);
			}
		}
		return codeblocks;
	}
}
