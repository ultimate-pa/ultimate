package de.uni_freiburg.informatik.ultimate.lib.logicalinterpretation.cfgpreprocessing;

import java.util.ArrayDeque;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.GenericLabeledGraph;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.ILabeledGraph;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

public class CfgPreprocessor {

	private final IIcfg<IcfgLocation> mIcfg;
	private GenericLabeledGraph<IcfgLocation, IIcfgTransition<IcfgLocation>> mCurrentProcedureGraph;
	private final Queue<IcfgLocation> mWork = new ArrayDeque<>();
	
	public CfgPreprocessor(final IIcfg<IcfgLocation> icfg) {
		mIcfg = icfg;
	}

	public ILabeledGraph<IcfgLocation, IIcfgTransition<IcfgLocation>> graphOfProcedure(String procedureName) {
		mCurrentProcedureGraph = new GenericLabeledGraph<>();
		mWork.clear();

		// TODO Difference ProcedureEntryNodes and InitialNodes? Where to start?
		final IcfgLocation entryNode = mIcfg.getProcedureEntryNodes().get(procedureName);
		final IcfgLocation exitNode = mIcfg.getProcedureExitNodes().get(procedureName);
		final Set<IcfgLocation> errorNodes = mIcfg.getProcedureErrorNodes().get(procedureName);

		// TODO has entry/init incoming edges which should not be processed?
		processBackwards(exitNode);
		for (final IcfgLocation errorNode : errorNodes) {
			processBackwards(errorNode);
		}
		// TODO mark exit and error nodes in procedure graph?

		return mCurrentProcedureGraph;
	}

	private void processBackwards(IcfgLocation node) {
		// for cases in which node has no edges or self loops
		mCurrentProcedureGraph.addNode(node);

		mWork.add(node);
		while (!mWork.isEmpty()) {
			node = mWork.remove();
			for (IcfgEdge edge : node.getIncomingEdges()) {
				processBackwards(edge);
			}
		}
	}

	private void processBackwards(final IcfgEdge regularEdge) {
		addToWorklistIfNew(regularEdge.getSource());
		copyEdge(regularEdge);
	}

	private void copyEdge(final IcfgEdge edge) {
		mCurrentProcedureGraph.addEdge(edge.getSource(), edge, edge.getTarget());
	}

	private void processBackwards(
			final IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> returnEdge) {
		final IIcfgCallTransition<IcfgLocation> correspondingCallEdge = returnEdge.getCorrespondingCall();
		final IcfgLocation correspondingSource = correspondingCallEdge.getSource();
		addToWorklistIfNew(correspondingSource);
		// Summary edge representing call/return to/from a procedure.
		// Summary edges do not summarize the procedure.
		// They are just there to point out, that we skipped the procedure.
		mCurrentProcedureGraph.addEdge(correspondingCallEdge.getSource(),
				new CallReturnSummary(correspondingCallEdge, returnEdge),
				returnEdge.getTarget());
		// Dead end edge representing the possibility to enter a procedure without returning due to an error
		mCurrentProcedureGraph.addEdge(correspondingCallEdge.getSource(),
				correspondingCallEdge,
				returnEdge.getTarget());
	}

	private void processBackwards(final IIcfgCallTransition<IcfgLocation> callEdge) {
		// nothing to do
		// TODO assert callEdge.getSource() == initial node?
		// TODO mark initial node in procedure graph?
	}

	private void addToWorklistIfNew(final IcfgLocation node) {
		if (!mCurrentProcedureGraph.getNodes().contains(node)) {
			mWork.add(node);
		}
	}
}
