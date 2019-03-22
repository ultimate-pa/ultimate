package de.uni_freiburg.informatik.ultimate.lib.logicalinterpretation.cfgpreprocessing;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.GenericLabeledGraph;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.ILabeledGraph;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;

// TODO Introduce <LOC extends IcfgLocation> ?
public class CfgPreprocessor {

	private final IIcfg<IcfgLocation> mIcfg;
	private GenericLabeledGraph<IcfgLocation, TransFormula> mCurrentProcedureGraph;
	private final Queue<IcfgLocation> mWork = new ArrayDeque<>();
	
	public CfgPreprocessor(final IIcfg<IcfgLocation> icfg) {
		mIcfg = icfg;
	}

	public ILabeledGraph<IcfgLocation, TransFormula>  graphOfProcedure(String procedureName) {
		mCurrentProcedureGraph = new GenericLabeledGraph<>();
		mWork.clear();

		final IcfgLocation entryNode = mIcfg.getProcedureEntryNodes().get(procedureName);
		final IcfgLocation exitNode = mIcfg.getProcedureExitNodes().get(procedureName);
		final Set<IcfgLocation> errorNodes = mIcfg.getProcedureErrorNodes().get(procedureName);

		// TODO Difference ProcedureEntryNodes and InitialNodes? Where to start?
		// TODO has entry/init incoming edges which should not be processed?
		processBackwards(exitNode);
		for (final IcfgLocation errorNode : errorNodes) {
			processBackwards(errorNode);
		}

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

	private void processBackwards(final IcfgEdge nonReturnEdge) {
		addToWorklistIfNew(nonReturnEdge.getSource());
		copyEdge(nonReturnEdge);
	}

	private void copyEdge(final IcfgEdge edge) {
		mCurrentProcedureGraph.addEdge(edge.getSource(), edge.getTransformula(), edge.getTarget());
	}

	private void processBackwards(final IIcfgReturnTransition<?, ?> returnEdge) {
		final IIcfgCallTransition correspondingCallEdge = returnEdge.getCorrespondingCall();
		final IcfgLocation correspondingSource = correspondingCallEdge.getSource();
		addToWorklistIfNew(correspondingSource);
		// TODO add special "SUM F" edge (shortcut). Start at correspondingSource
		// TODO add special "CALL F" edge (dead end). Start at correspondingSource
	}
	
	private void addToWorklistIfNew(final IcfgLocation node) {
		if (!mCurrentProcedureGraph.getNodes().contains(node)) {
			mWork.add(node);
		}
	}
}
