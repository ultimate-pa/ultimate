/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.translation.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.ProgramExecutionFormatter;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class BlockEncodingBacktranslator extends DefaultTranslator<IcfgEdge, IcfgEdge, Term, Term, IcfgLocation, IcfgLocation> {

	private static final boolean PRINT_MAPPINGS = false;

	private final Map<IcfgEdge, List<IcfgEdge>> mEdgeMapping;
	private final Map<IcfgLocation, IcfgLocation> mLocationMapping;
	private final ILogger mLogger;
	private final Set<IcfgEdge> mIntermediateEdges;

	public BlockEncodingBacktranslator(final Class<IcfgEdge> traceElementType, final Class<Term> expressionType,
			final ILogger logger) {
		super(traceElementType, traceElementType, expressionType, expressionType);
		mEdgeMapping = new HashMap<>();
		mLocationMapping = new HashMap<>();
		mLogger = logger;
		mIntermediateEdges = new HashSet<>();
	}

	@SuppressWarnings("unchecked")
	@Override
	public IProgramExecution<IcfgEdge, Term> translateProgramExecution(final IProgramExecution<IcfgEdge, Term> pe) {
		if (pe == null) {
			throw new IllegalArgumentException("programExecution is null");
		}

		if (!(pe instanceof IcfgProgramExecution)) {
			throw new IllegalArgumentException("argument is not IcfgProgramExecution but " + pe.getClass());

		}
		final IcfgProgramExecution programExecution = ((IcfgProgramExecution) pe);
		final Map<TermVariable, Boolean>[] oldBranchEncoders = programExecution.getBranchEncoders();
		assert oldBranchEncoders.length == programExecution.getLength() : "wrong branchencoders";
		assert checkCallStackSourceProgramExecution(mLogger,
				programExecution) : "callstack of initial program execution already broken";

		final List<IcfgEdge> newTrace = new ArrayList<>();
		final List<ProgramState<Term>> newValues = new ArrayList<>();
		final List<Map<TermVariable, Boolean>> newBranchEncoders = new ArrayList<>();

		if (PRINT_MAPPINGS) {
			mLogger.info("Using the following mapping");
			for (final Entry<IcfgEdge, List<IcfgEdge>> entry : mEdgeMapping.entrySet()) {
				printMapping(entry.getKey(), entry.getValue());
			}
		}

		for (int i = 0; i < programExecution.getLength(); ++i) {
			final AtomicTraceElement<IcfgEdge> currentATE = programExecution.getTraceElement(i);
			final List<IcfgEdge> mappedEdges = mEdgeMapping.get(currentATE.getTraceElement());
			if (mappedEdges == null || mappedEdges.isEmpty()) {
				mLogger.warn("Skipped backtranslation of ATE [" + currentATE.getTraceElement().hashCode() + "] "
						+ currentATE.getTraceElement() + " because there is no mapped edge");
				continue;
			}
			final Iterator<IcfgEdge> iter = mappedEdges.iterator();
			while (iter.hasNext()) {
				newTrace.add(iter.next());
				if (iter.hasNext()) {
					newValues.add(null);
					newBranchEncoders.add(null);
				}
			}
			newValues.add(programExecution.getProgramState(i));
			newBranchEncoders.add(oldBranchEncoders[i]);

		}

		final Map<Integer, ProgramState<Term>> newValuesMap = new HashMap<>();
		newValuesMap.put(-1, programExecution.getInitialProgramState());
		for (int i = 0; i < newValues.size(); ++i) {
			newValuesMap.put(i, newValues.get(i));
		}

		final IcfgProgramExecution newPe = new IcfgProgramExecution(newTrace, newValuesMap,
				newBranchEncoders.toArray(new Map[newBranchEncoders.size()]));
		assert checkCallStackTargetProgramExecution(mLogger, newPe) : "callstack broke during translation";
		return newPe;
	}

	public void mapEdges(final IcfgEdge newEdge, final IcfgEdge originalEdge) {
		final List<IcfgEdge> limboEdges = mEdgeMapping.get(originalEdge);
		if (limboEdges != null) {
			// an intermediate edge is replaced by a new edge
			mIntermediateEdges.add(originalEdge);
			for (final IcfgEdge limboEdge : limboEdges) {
				mapEdges(newEdge, limboEdge);
			}
			return;
		}

		List<IcfgEdge> originalEdges = mEdgeMapping.get(newEdge);
		if (originalEdges == null) {
			originalEdges = new ArrayList<>();
			mEdgeMapping.put(newEdge, originalEdges);
		}
		originalEdges.add(originalEdge);
		if (PRINT_MAPPINGS) {
			printMapping(newEdge, originalEdges);
		}
	}

	public void removeIntermediateMappings() {
		if (mIntermediateEdges.isEmpty()) {
			return;
		}
		if (PRINT_MAPPINGS) {
			mLogger.info("Removing " + getCollectionString(mIntermediateEdges));
		}
		for (final IcfgEdge edge : mIntermediateEdges) {
			mEdgeMapping.remove(edge);
		}
		mIntermediateEdges.clear();
	}

	private void printMapping(final IcfgEdge newEdge, final List<IcfgEdge> originalEdges) {
		mLogger.info(
				markCodeblock(newEdge) + newEdge.hashCode() + " is mapped to " + getCollectionString(originalEdges));
	}

	private static String getCollectionString(final Collection<IcfgEdge> originalEdges) {
		return originalEdges.stream().map(a -> markCodeblock(a) + String.valueOf(a.hashCode()))
				.collect(Collectors.joining(","));
	}

	private static String markCodeblock(final IcfgEdge newEdge) {
		return "";
//		2018-09-14 Matthias: I commented the following lines to get rid
//		of the dependency to CodeBlock
//		if (newEdge instanceof CodeBlock) {
//			return "";
//		}
//		return "!";
	}

	public void mapLocations(final IcfgLocation newLoc, final IcfgLocation oldLoc) {
		final IcfgLocation realOldLoc = mLocationMapping.get(oldLoc);
		if (realOldLoc != null) {
			// this means we replaced an edge which we already replaced again
			// with something new, we have to map this to the real original
			mLocationMapping.put(newLoc, realOldLoc);
		} else {
			mLocationMapping.put(newLoc, oldLoc);
		}
	}

	/**
	 * @return Map from new locations to old locations.
	 */
	public Map<IcfgLocation, IcfgLocation> getLocationMapping() {
		return Collections.unmodifiableMap(mLocationMapping);
	}

	/**
	 * @deprecated In general, new edges can be mapped to multiple old edges. Therefore, you need to work with an edge
	 *             mapping from edge to list of edges.
	 * @return Map from new edges to old edges.
	 */
	@Deprecated
	public Map<IcfgEdge, IcfgEdge> getEdgeMapping() {
		final Map<IcfgEdge, IcfgEdge> rtr = new HashMap<>();
		for (final Entry<IcfgEdge, List<IcfgEdge>> entry : mEdgeMapping.entrySet()) {
			if (entry.getValue().size() > 1) {
				throw new UnsupportedOperationException(
						"The new edge " + entry.getKey() + " is mapped to multiple edges");
			}
			rtr.put(entry.getKey(), entry.getValue().isEmpty() ? null : entry.getValue().get(0));
		}
		return rtr;
	}

	@Override
	protected void printBrokenCallStackSource(final List<AtomicTraceElement<IcfgEdge>> trace,
			final int breakpointIndex) {
		final List<IcfgEdge> teList =
				trace.stream().limit(breakpointIndex).map(a -> a.getTraceElement()).collect(Collectors.toList());
		mLogger.fatal(new ProgramExecutionFormatter<>(new IcfgBacktranslationValueProvider())
				.formatProgramExecution(new IcfgProgramExecution(teList, Collections.emptyMap())));
	}

	@Override
	protected void printBrokenCallStackTarget(final List<AtomicTraceElement<IcfgEdge>> trace,
			final int breakpointIndex) {
		printBrokenCallStackSource(trace, breakpointIndex);
	}
}
