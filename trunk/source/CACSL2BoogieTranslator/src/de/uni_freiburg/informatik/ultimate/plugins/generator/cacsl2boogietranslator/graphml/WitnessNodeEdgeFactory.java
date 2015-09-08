/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.graphml;

import org.eclipse.cdt.core.dom.ast.IASTExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.result.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;

public class WitnessNodeEdgeFactory {

	private long mCurrentNodeId;
	private long mCurrentEdgeId;

	public WitnessNodeEdgeFactory() {
		mCurrentNodeId = -1;
		mCurrentEdgeId = -1;
	}

	public WitnessNode createWitnessNode() {
		return createWitnessNode(false, false, false);
	}

	public WitnessNode createInitialWitnessNode() {
		return createWitnessNode(true, false, false);
	}

	public WitnessNode createErrorWitnessNode() {
		return createWitnessNode(false, true, false);
	}

	public WitnessNode createWitnessNode(boolean isInitial, boolean isError, boolean isSink) {
		mCurrentNodeId++;
		return new WitnessNode(mCurrentNodeId, isInitial, isError, isSink);
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
