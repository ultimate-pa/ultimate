/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.cfgpreprocessing;

import java.util.ArrayDeque;
import java.util.Queue;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.ILabeledGraph;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

public class CfgPreprocessor {

	private final IIcfg<IcfgLocation> mIcfg;
	private ProcedureGraph mCurrentProcedureGraph;
	private final Queue<IcfgLocation> mWork = new ArrayDeque<>();
	
	public CfgPreprocessor(final IIcfg<IcfgLocation> icfg) {
		mIcfg = icfg;
	}

	public ProcedureGraph graphOfProcedure(final String procedureName) {
		mCurrentProcedureGraph = new ProcedureGraph(mIcfg, procedureName);
		mWork.clear();
		mWork.add(mCurrentProcedureGraph.getExitNode());
		mWork.addAll(mCurrentProcedureGraph.getErrorNodes());
		while (!mWork.isEmpty()) {
			for (IcfgEdge edge : mWork.remove().getIncomingEdges()) {
				processBottomUp(edge);
			}
		}
		return mCurrentProcedureGraph;
	}

	@SuppressWarnings("unchecked")
	private void processBottomUp(final IcfgEdge edge) {
		if (edge instanceof IIcfgReturnTransition<?,?>) {
			processReturn((IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>>) edge);
		} else if (edge instanceof IIcfgCallTransition<?>) {
			processCall((IIcfgCallTransition<IcfgLocation>) edge);
		} else {
			addToWorklistIfNew(edge.getSource());
			copyEdge(edge);
		}
	}

	private void processReturn(
			final IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> returnEdge) {
		final IIcfgCallTransition<IcfgLocation> correspondingCallEdge = returnEdge.getCorrespondingCall();
		final IcfgLocation correspondingSource = correspondingCallEdge.getSource();
		addToWorklistIfNew(correspondingSource);
		// Summary edge representing call/return to/from a procedure.
		// Summary edges do not summarize the procedure.
		// They are just there to point out, that we skipped the procedure.
		mCurrentProcedureGraph.addEdge(correspondingCallEdge.getSource(),
				new CallReturnSummary(correspondingCallEdge, returnEdge),
				correspondingCallEdge.getTarget());
		// Dead end edge representing the possibility to enter a procedure without returning due to an error
		mCurrentProcedureGraph.addEdge(correspondingCallEdge.getSource(),
				correspondingCallEdge,
				returnEdge.getTarget());
	}

	private void processCall(final IIcfgCallTransition<IcfgLocation> callEdge) {
		assert callEdge.getSource() == mCurrentProcedureGraph.getEntryNode();
		// nothing to do
	}

	private void addToWorklistIfNew(final IcfgLocation node) {
		if (!mCurrentProcedureGraph.getNodes().contains(node)) {
			mWork.add(node);
		}
	}

	private void copyEdge(final IcfgEdge edge) {
		mCurrentProcedureGraph.addEdge(edge.getSource(), edge, edge.getTarget());
	}
}
