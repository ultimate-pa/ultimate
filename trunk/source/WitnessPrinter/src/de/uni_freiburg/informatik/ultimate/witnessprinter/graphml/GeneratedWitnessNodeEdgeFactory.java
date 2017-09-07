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
package de.uni_freiburg.informatik.ultimate.witnessprinter.graphml;

import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;

public class GeneratedWitnessNodeEdgeFactory<TE, E> {

	private long mCurrentNodeId;
	private long mCurrentEdgeId;
	private final IBacktranslationValueProvider<TE, E> mStringProvider;

	public GeneratedWitnessNodeEdgeFactory(final IBacktranslationValueProvider<TE, E> stringProvider) {
		assert stringProvider != null;
		mStringProvider = stringProvider;
		mCurrentNodeId = -1;
		mCurrentEdgeId = -1;
	}

	public GeneratedWitnessNode createWitnessNode() {
		return createWitnessNode(false, false, false);
	}

	public GeneratedWitnessNode createInitialWitnessNode() {
		return createWitnessNode(true, false, false);
	}

	public GeneratedWitnessNode createErrorWitnessNode() {
		return createWitnessNode(false, true, false);
	}

	public GeneratedWitnessNode createWitnessNode(final boolean isInitial, final boolean isError,
			final boolean isSink) {
		mCurrentNodeId++;
		return new GeneratedWitnessNode(mCurrentNodeId, isInitial, isError, isSink);
	}

	public GeneratedWitnessEdge<TE, E> createWitnessEdge(final AtomicTraceElement<TE> traceElement,
			final ProgramState<E> state) {
		mCurrentEdgeId++;
		return new GeneratedWitnessEdge<>(traceElement, state, false, mStringProvider, mCurrentEdgeId);
	}

	public GeneratedWitnessEdge<TE, E> createWitnessEdge(final AtomicTraceElement<TE> traceElement) {
		return createWitnessEdge(traceElement, false);
	}

	public GeneratedWitnessEdge<TE, E> createDummyWitnessEdge() {
		mCurrentEdgeId++;
		return new GeneratedWitnessEdge<>(null, null, false, mStringProvider, mCurrentEdgeId);
	}

	public GeneratedWitnessEdge<TE, E> createWitnessEdge(final AtomicTraceElement<TE> traceElement,
			final boolean isEnteringLoopHead) {
		mCurrentEdgeId++;
		return new GeneratedWitnessEdge<>(traceElement, null, isEnteringLoopHead, mStringProvider, mCurrentEdgeId);
	}
}
