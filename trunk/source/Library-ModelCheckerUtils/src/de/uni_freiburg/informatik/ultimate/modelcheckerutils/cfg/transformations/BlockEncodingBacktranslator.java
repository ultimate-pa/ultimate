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
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.translation.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.ProgramExecutionFormatter;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.AtomicTraceElementBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class BlockEncodingBacktranslator extends
		DefaultTranslator<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>, Term, Term, IcfgLocation, IcfgLocation> {

	private static final boolean PRINT_MAPPINGS = false;

	private final Map<IIcfgTransition<IcfgLocation>, List<IIcfgTransition<IcfgLocation>>> mEdgeMapping;
	private final Map<IcfgLocation, IcfgLocation> mLocationMapping;
	private final ILogger mLogger;
	private final Set<IIcfgTransition<IcfgLocation>> mIntermediateEdges;
	/**
	 * Function that determines how expression (here {@link Term}s) are translated. By default we use the identity.
	 */
	private Function<Term, Term> mTermTranslator = (x -> x);
	/**
	 * Set of variables that are removed from {@link ProgramState}s. By default we use the empty set. (This can be
	 * helpful for auxiliary variables that we cannot translate).
	 */
	private Set<Term> mVariableBlacklist = Collections.emptySet();

	public BlockEncodingBacktranslator(final Class<? extends IIcfgTransition<IcfgLocation>> traceElementType,
			final Class<Term> expressionType, final ILogger logger) {
		super(traceElementType, traceElementType, expressionType, expressionType);
		mEdgeMapping = new HashMap<>();
		mLocationMapping = new HashMap<>();
		mLogger = logger;
		mIntermediateEdges = new HashSet<>();
	}

	@SuppressWarnings("unchecked")
	@Override
	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term>
			translateProgramExecution(final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> oldPe) {
		if (oldPe == null) {
			throw new IllegalArgumentException("programExecution is null");
		}

		if (!(oldPe instanceof IcfgProgramExecution)) {
			throw new IllegalArgumentException("argument is not IcfgProgramExecution but " + oldPe.getClass());

		}
		final IcfgProgramExecution oldIcfgPe = ((IcfgProgramExecution) oldPe);
		final Map<TermVariable, Boolean>[] oldBranchEncoders = oldIcfgPe.getBranchEncoders();
		assert oldBranchEncoders.length == oldIcfgPe.getLength() : "wrong branchencoders";
		assert checkCallStackSourceProgramExecution(mLogger,
				oldIcfgPe) : "callstack of initial program execution already broken";

		final List<AtomicTraceElement<IIcfgTransition<IcfgLocation>>> newTrace = new ArrayList<>();
		final List<ProgramState<Term>> newValues = new ArrayList<>();
		final List<Map<TermVariable, Boolean>> newBranchEncoders = new ArrayList<>();

		if (PRINT_MAPPINGS) {
			mLogger.info("Using the following mapping");
			for (final Entry<IIcfgTransition<IcfgLocation>, List<IIcfgTransition<IcfgLocation>>> entry : mEdgeMapping
					.entrySet()) {
				printMapping(entry.getKey(), entry.getValue());
			}
		}

		for (int i = 0; i < oldIcfgPe.getLength(); ++i) {
			final AtomicTraceElement<IIcfgTransition<IcfgLocation>> currentATE = oldIcfgPe.getTraceElement(i);
			final List<IIcfgTransition<IcfgLocation>> mappedEdges = mEdgeMapping.get(currentATE.getTraceElement());
			if (mappedEdges == null || mappedEdges.isEmpty()) {
				mLogger.warn("Skipped backtranslation of ATE [" + currentATE.getTraceElement().hashCode() + "] "
						+ currentATE.getTraceElement() + " because there is no mapped edge");
				continue;
			}
			final Iterator<IIcfgTransition<IcfgLocation>> iter = mappedEdges.iterator();
			while (iter.hasNext()) {
				final IIcfgTransition<IcfgLocation> currentEdge = iter.next();
				newTrace.add(AtomicTraceElementBuilder.fromReplaceElementAndStep(currentATE, currentEdge).build());
				if (iter.hasNext()) {
					newValues.add(null);
					newBranchEncoders.add(null);
				}
			}
			final ProgramState<Term> newProgramState = translateProgramState(oldIcfgPe.getProgramState(i));
			newValues.add(newProgramState);
			newBranchEncoders.add(oldBranchEncoders[i]);

		}

		final Map<Integer, ProgramState<Term>> newValuesMap = new HashMap<>();
		newValuesMap.put(-1, oldIcfgPe.getInitialProgramState());
		for (int i = 0; i < newValues.size(); ++i) {
			newValuesMap.put(i, newValues.get(i));
		}

		final IcfgProgramExecution newPe = new IcfgProgramExecution(newTrace, newValuesMap,
				newBranchEncoders.toArray(new Map[newBranchEncoders.size()]), oldIcfgPe.isConcurrent());
		assert checkCallStackTargetProgramExecution(mLogger, newPe) : "callstack broke during translation";
		return newPe;
	}

	public void mapEdges(final IIcfgTransition<IcfgLocation> newEdge,
			final IIcfgTransition<IcfgLocation> originalEdge) {
		final List<IIcfgTransition<IcfgLocation>> limboEdges = mEdgeMapping.get(originalEdge);
		if (limboEdges != null) {
			// an intermediate edge is replaced by a new edge
			mIntermediateEdges.add(originalEdge);
			for (final IIcfgTransition<IcfgLocation> limboEdge : limboEdges) {
				mapEdges(newEdge, limboEdge);
			}
			return;
		}

		List<IIcfgTransition<IcfgLocation>> originalEdges = mEdgeMapping.get(newEdge);
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
		for (final IIcfgTransition<IcfgLocation> edge : mIntermediateEdges) {
			mEdgeMapping.remove(edge);
		}
		mIntermediateEdges.clear();
	}

	private void printMapping(final IIcfgTransition<IcfgLocation> newEdge,
			final List<IIcfgTransition<IcfgLocation>> originalEdges) {
		mLogger.info(
				markCodeblock(newEdge) + newEdge.hashCode() + " is mapped to " + getCollectionString(originalEdges));
	}

	private static String getCollectionString(final Collection<IIcfgTransition<IcfgLocation>> originalEdges) {
		return originalEdges.stream().map(a -> markCodeblock(a) + String.valueOf(a.hashCode()))
				.collect(Collectors.joining(","));
	}

	private static String markCodeblock(final IIcfgTransition<IcfgLocation> newEdge) {
		return "";
		// 2018-09-14 Matthias: I commented the following lines to get rid
		// of the dependency to CodeBlock
		// if (newEdge instanceof CodeBlock) {
		// return "";
		// }
		// return "!";
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
	public Map<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>> getEdgeMapping() {
		final Map<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>> rtr = new HashMap<>();
		for (final Entry<IIcfgTransition<IcfgLocation>, List<IIcfgTransition<IcfgLocation>>> entry : mEdgeMapping
				.entrySet()) {
			if (entry.getValue().size() > 1) {
				throw new UnsupportedOperationException(
						"The new edge " + entry.getKey() + " is mapped to multiple edges");
			}
			rtr.put(entry.getKey(), entry.getValue().isEmpty() ? null : entry.getValue().get(0));
		}
		return rtr;
	}

	@Override
	protected void printBrokenCallStackSource(final List<AtomicTraceElement<IIcfgTransition<IcfgLocation>>> trace,
			final int breakpointIndex) {
		final List<IIcfgTransition<IcfgLocation>> teList =
				trace.stream().limit(breakpointIndex).map(a -> a.getTraceElement()).collect(Collectors.toList());
		mLogger.fatal(new ProgramExecutionFormatter<>(new IcfgBacktranslationValueProvider())
				.formatProgramExecution(IcfgProgramExecution.create(teList, Collections.emptyMap())));
	}

	@Override
	protected void printBrokenCallStackTarget(final List<AtomicTraceElement<IIcfgTransition<IcfgLocation>>> trace,
			final int breakpointIndex) {
		printBrokenCallStackSource(trace, breakpointIndex);
	}

	public void setTermTranslator(final Function<Term, Term> termTranslator) {
		mTermTranslator = termTranslator;
	}

	@Override
	public Term translateExpression(final Term expression) {
		final Term result = mTermTranslator.apply(expression);
		return result;
	}

	@Override
	public ProgramState<Term> translateProgramState(final ProgramState<Term> oldProgramState) {
		if (oldProgramState == null) {
			return null;
		}
		final Map<Term, Collection<Term>> variable2Values = new HashMap<>();
		for (final Term oldVariable : oldProgramState.getVariables()) {
			if (mVariableBlacklist.contains(oldVariable)) {
				continue;
			}
			final Term newVariable = translateExpression(oldVariable);
			final Collection<Term> newValues = new ArrayList<>();
			for (final Term oldValue : oldProgramState.getValues(oldVariable)) {
				newValues.add(translateExpression(oldValue));
			}
			variable2Values.put(newVariable, newValues);
		}
		return new ProgramState<>(variable2Values);
	}

	public void setVariableBlacklist(final Set<Term> variableBlacklist) {
		mVariableBlacklist = variableBlacklist;
	}

}
