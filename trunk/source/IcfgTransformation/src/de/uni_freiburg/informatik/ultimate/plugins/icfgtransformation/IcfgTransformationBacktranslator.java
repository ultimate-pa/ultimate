/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncodingV2 plug-in.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncodingV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncodingV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncodingV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtransformation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.translation.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class IcfgTransformationBacktranslator extends
		DefaultTranslator<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>, Term, Term, String, String> {

	private final Map<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>> mEdgeMapping;
	private final ILogger mLogger;

	public IcfgTransformationBacktranslator(final Class<? extends IIcfgTransition<IcfgLocation>> traceElementType,
			final Class<Term> expressionType, final ILogger logger) {
		super(traceElementType, traceElementType, expressionType, expressionType);
		mEdgeMapping = new HashMap<>();
		mLogger = logger;
	}

	@SuppressWarnings("unchecked")
	@Override
	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term>
			translateProgramExecution(final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> programExecution) {

		Map<TermVariable, Boolean>[] oldBranchEncoders = null;
		if (programExecution instanceof IcfgProgramExecution) {
			oldBranchEncoders = ((IcfgProgramExecution) programExecution).getBranchEncoders();
		}

		final List<IIcfgTransition<IcfgLocation>> newTrace = new ArrayList<>();
		final Map<Integer, ProgramState<Term>> newValues = new HashMap<>();
		final List<Map<TermVariable, Boolean>> newBranchEncoders = new ArrayList<>();

		addProgramState(-1, newValues, programExecution.getInitialProgramState());

		for (int i = 0; i < programExecution.getLength(); ++i) {
			final AtomicTraceElement<IIcfgTransition<IcfgLocation>> currentATE = programExecution.getTraceElement(i);
			final IIcfgTransition<IcfgLocation> mappedEdge = mEdgeMapping.get(currentATE.getTraceElement());
			if (mappedEdge == null || !(mappedEdge instanceof CodeBlock)) {
				// skip this, its not worth it.
				mLogger.info("Skipped ATE [" + currentATE.getTraceElement().hashCode() + "] "
						+ currentATE.getTraceElement());
				continue;
			}
			newTrace.add(mappedEdge);
			addProgramState(i, newValues, programExecution.getProgramState(i));
			if (oldBranchEncoders != null && oldBranchEncoders.length > i) {
				newBranchEncoders.add(oldBranchEncoders[i]);
			}
		}

		return IcfgProgramExecution.create(newTrace, newValues,
				newBranchEncoders.toArray(new Map[newBranchEncoders.size()]));
	}

	private static void addProgramState(final Integer i, final Map<Integer, ProgramState<Term>> newValues,
			final ProgramState<Term> programState) {
		newValues.put(i, programState);
	}

	public void mapEdges(final IIcfgTransition<IcfgLocation> newEdge,
			final IIcfgTransition<IcfgLocation> originalEdge) {
		final IIcfgTransition<IcfgLocation> realOriginalEdge = mEdgeMapping.get(originalEdge);
		if (realOriginalEdge != null) {
			// this means we replaced an edge which we already replaced again
			// with something new, we have to map this to the real original
			mEdgeMapping.put(newEdge, realOriginalEdge);
		} else {
			mEdgeMapping.put(newEdge, originalEdge);
		}
	}
}
