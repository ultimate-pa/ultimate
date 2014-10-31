package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.graphml;

import org.eclipse.cdt.core.dom.ast.IASTExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;

public class WitnessNodeEdgeFactory {

	private long mCurrentNodeId;
	private long mCurrentEdgeId;

	public WitnessNodeEdgeFactory() {
		mCurrentNodeId = -1;
		mCurrentEdgeId = -1;
	}

	public WitnessNode createWitnessNode() {
		mCurrentNodeId++;
		return new WitnessNode(false, mCurrentNodeId);
	}

	public WitnessNode createWitnessNode(boolean isEntry) {
		mCurrentNodeId++;
		return new WitnessNode(isEntry, mCurrentNodeId);
	}

	public WitnessEdge createWitnessEdge(AtomicTraceElement<CACSLLocation> traceElement,
			ProgramState<IASTExpression> state) {
		mCurrentEdgeId++;
		return new WitnessEdge(traceElement, state, mCurrentEdgeId);
	}

	public WitnessEdge createWitnessEdge(AtomicTraceElement<CACSLLocation> traceElement) {
		mCurrentEdgeId++;
		return new WitnessEdge(traceElement, null, mCurrentEdgeId);
	}

	public WitnessEdge createWitnessEdge(ProgramState<IASTExpression> state) {
		mCurrentEdgeId++;
		return new WitnessEdge(null, state, mCurrentEdgeId);
	}

	public WitnessEdge createDummyWitnessEdge() {
		mCurrentEdgeId++;
		return new WitnessEdge(null, null, mCurrentEdgeId);
	}

}
