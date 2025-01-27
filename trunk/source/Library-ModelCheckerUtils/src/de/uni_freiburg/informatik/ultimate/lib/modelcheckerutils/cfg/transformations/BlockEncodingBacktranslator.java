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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations;

import java.util.ArrayDeque;
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
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.translation.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.ProgramExecutionFormatter;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.AtomicTraceElementBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class BlockEncodingBacktranslator extends
		DefaultTranslator<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>, Term, Term, IcfgLocation, IcfgLocation, ILocation> {

	private static final boolean PRINT_MAPPINGS = false;

	private final Map<IIcfgTransition<IcfgLocation>, List<IIcfgTransition<IcfgLocation>>> mSequentialCompositions =
			new HashMap<>();
	private final Map<IIcfgTransition<IcfgLocation>, Set<IIcfgTransition<IcfgLocation>>> mParallelCompositions =
			new HashMap<>();
	private final Map<IIcfgTransition<IcfgLocation>, TermVariable> mBranchEncoderMapping = new HashMap<>();

	private final Map<IIcfgTransition<IcfgLocation>, Consumer<AtomicTraceElementBuilder<IIcfgTransition<IcfgLocation>>>> mAteTransformer =
			new HashMap<>();

	private final Map<IcfgLocation, IcfgLocation> mLocationMapping = new HashMap<>();
	private final ILogger mLogger;
	private final Set<IIcfgTransition<IcfgLocation>> mIntermediateEdges = new HashSet<>();
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
		mLogger = logger;
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
		final IcfgProgramExecution<IIcfgTransition<IcfgLocation>> oldIcfgPe =
				((IcfgProgramExecution<IIcfgTransition<IcfgLocation>>) oldPe);
		final Map<TermVariable, Boolean>[] oldBranchEncoders = oldIcfgPe.getBranchEncoders();
		assert oldBranchEncoders.length == oldIcfgPe.getLength() : "incorrect number of branch encoders: expected "
				+ oldIcfgPe.getLength() + ", actual " + oldBranchEncoders.length;
		assert checkCallStackSourceProgramExecution(mLogger,
				oldIcfgPe) : "callstack of initial program execution already broken";

		final List<AtomicTraceElement<IIcfgTransition<IcfgLocation>>> newTrace = new ArrayList<>();
		final List<ProgramState<Term>> newValues = new ArrayList<>();
		final List<Map<TermVariable, Boolean>> newBranchEncoders = new ArrayList<>();

		if (PRINT_MAPPINGS) {
			mLogger.info("Using the following mapping");
			for (final Entry<IIcfgTransition<IcfgLocation>, List<IIcfgTransition<IcfgLocation>>> entry : mSequentialCompositions
					.entrySet()) {
				printMapping(entry.getKey(), entry.getValue());
			}
		}

		for (int i = 0; i < oldIcfgPe.getLength(); ++i) {
			final AtomicTraceElement<IIcfgTransition<IcfgLocation>> currentATE = oldIcfgPe.getTraceElement(i);
			final Collection<IIcfgTransition<IcfgLocation>> mappedEdges =
					translateBack(currentATE.getTraceElement(), oldBranchEncoders[i]);

			final Iterator<IIcfgTransition<IcfgLocation>> iter = mappedEdges.iterator();
			while (iter.hasNext()) {
				final IIcfgTransition<IcfgLocation> currentEdge = iter.next();
				final AtomicTraceElementBuilder<IIcfgTransition<IcfgLocation>> builder =
						AtomicTraceElementBuilder.fromReplaceElementAndStep(currentATE, currentEdge);
				final var transformer = mAteTransformer.get(currentATE.getTraceElement());
				if (transformer != null) {
					transformer.accept(builder);
				}
				newTrace.add(builder.build());
				if (iter.hasNext()) {
					newValues.add(null);
					newBranchEncoders.add(oldBranchEncoders[i]);
				}
			}
			final ProgramState<Term> newProgramState = translateProgramState(oldIcfgPe.getProgramState(i));
			newValues.add(newProgramState);
			newBranchEncoders.add(oldBranchEncoders[i]);

		}

		final Map<Integer, ProgramState<Term>> newValuesMap = new HashMap<>();
		newValuesMap.put(-1, translateProgramState(oldIcfgPe.getInitialProgramState()));
		for (int i = 0; i < newValues.size(); ++i) {
			newValuesMap.put(i, newValues.get(i));
		}

		final IcfgProgramExecution<IIcfgTransition<IcfgLocation>> newPe = new IcfgProgramExecution<>(newTrace,
				newValuesMap, newBranchEncoders.toArray(new Map[newBranchEncoders.size()]), oldIcfgPe.isConcurrent(),
				IcfgProgramExecution.getClassFromAtomicTraceElements(newTrace));
		assert checkCallStackTargetProgramExecution(mLogger, newPe) : "callstack broke during translation";
		return newPe;
	}

	/**
	 * Translate a transition that is the result of arbitrarily nested sequential and choice compositions back to the
	 * sequence of original transitions.
	 *
	 * @param transition
	 *            The transition to translate back.
	 * @param branchEncoders
	 *            Branch encoders indicating which branch of a choice composition was taken.
	 */
	private Collection<IIcfgTransition<IcfgLocation>> translateBack(final IIcfgTransition<IcfgLocation> transition,
			final Map<TermVariable, Boolean> branchEncoders) {
		final ArrayDeque<IIcfgTransition<IcfgLocation>> result = new ArrayDeque<>();

		final ArrayDeque<IIcfgTransition<IcfgLocation>> stack = new ArrayDeque<>();
		stack.push(transition);

		while (!stack.isEmpty()) {
			final IIcfgTransition<IcfgLocation> current = stack.pop();

			if (mSequentialCompositions.containsKey(current)) {
				final List<IIcfgTransition<IcfgLocation>> sequence = mSequentialCompositions.get(current);
				assert sequence != null;

				// Put the transitions making up this composition on the stack.
				// Last transition in the sequence is on top.
				for (final IIcfgTransition<IcfgLocation> component : sequence) {
					stack.push(component);
				}
			} else if (mParallelCompositions.containsKey(current)) {
				final Set<IIcfgTransition<IcfgLocation>> choices = mParallelCompositions.get(current);
				assert choices != null;

				if (branchEncoders == null) {
					mLogger.warn("Failed to translate choice composition: Branch encoders not available.");
					result.addFirst(current);
					continue;
				}

				boolean choiceFound = false;
				for (final IIcfgTransition<IcfgLocation> choice : choices) {
					assert mBranchEncoderMapping.get(choice) != null : "Choice composition is missing branch encoder";
					final TermVariable indicator = mBranchEncoderMapping.get(choice);
					assert branchEncoders.get(indicator) != null : "Branch indicator value was unknown";
					if (branchEncoders.get(indicator)) {
						stack.push(choice);
						choiceFound = true;
						break;
					}
				}
				assert choiceFound : "Could not determine correct choice for choice composition";
				// Note: We do not check that ONLY one choice is possible. For instance,
				// TraceCheckUtils#computeSomeIcfgProgramExecutionWithoutValues sets all branch encoders to true.
			} else {
				// Transition is assumed to be original.
				// As the last transition of a sequence is handled first (top of stack, see
				// above), we must prepend this transition to the result (instead of appending).
				result.addFirst(current);
			}
		}
		return result;
	}

	/**
	 * Maps edges composed with sequential composition to the original edges.
	 *
	 * @param newEdge
	 *            The sequential composition
	 * @param originalEdge
	 *            The original edge involved in the composition
	 */
	public void mapEdges(final IIcfgTransition<IcfgLocation> newEdge,
			final IIcfgTransition<IcfgLocation> originalEdge) {
		final List<IIcfgTransition<IcfgLocation>> limboEdges = mSequentialCompositions.get(originalEdge);
		if (limboEdges != null) {
			// an intermediate edge is replaced by a new edge
			mIntermediateEdges.add(originalEdge);
			for (final IIcfgTransition<IcfgLocation> limboEdge : limboEdges) {
				mapEdges(newEdge, limboEdge);
			}
			return;
		}

		final List<IIcfgTransition<IcfgLocation>> originalEdges =
				mSequentialCompositions.computeIfAbsent(newEdge, x -> new ArrayList<>());
		originalEdges.add(originalEdge);
		if (PRINT_MAPPINGS) {
			printMapping(newEdge, originalEdges);
		}
	}

	/**
	 * Maps edges composed with parallel composition to the original edges.
	 *
	 * @param newEdge
	 *            The parallel composition
	 * @param originalEdges
	 *            A mapping from branch encoders to the composed edges
	 */
	public void mapEdges(final IIcfgTransition<IcfgLocation> newEdge,
			final Map<TermVariable, IIcfgTransition<IcfgLocation>> originalEdges) {

		for (final Map.Entry<TermVariable, IIcfgTransition<IcfgLocation>> entry : originalEdges.entrySet()) {
			mapEdges(newEdge, entry.getValue(), entry.getKey());
		}
	}

	/**
	 * Maps edges composed with parallel composition to the original edges.
	 *
	 * @param newEdge
	 *            The parallel composition
	 * @param originalEdge
	 *            One of the edges that was composed
	 * @param branchEncoder
	 *            The branch encoder belonging to the original egde
	 */
	public void mapEdges(final IIcfgTransition<IcfgLocation> newEdge, final IIcfgTransition<IcfgLocation> originalEdge,
			final TermVariable branchEncoder) {
		final TermVariable oldEncoder = mBranchEncoderMapping.get(originalEdge);
		assert oldEncoder == null || oldEncoder == branchEncoder : "Ambiguous branch encoder for transition";
		mBranchEncoderMapping.put(originalEdge, branchEncoder);

		final Set<IIcfgTransition<IcfgLocation>> limboEdges = mParallelCompositions.get(originalEdge);
		if (limboEdges != null) {
			mIntermediateEdges.add(originalEdge);
			for (final IIcfgTransition<IcfgLocation> limboEdge : limboEdges) {
				mapEdges(newEdge, limboEdge, mBranchEncoderMapping.get(limboEdge));
			}
			return;
		}

		final Set<IIcfgTransition<IcfgLocation>> originalEdges =
				mParallelCompositions.computeIfAbsent(newEdge, x -> new HashSet<>());
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
			assert mSequentialCompositions.values().stream().noneMatch(
					s -> s.contains(edge)) : "Intermediate edge should not be used in sequential composition";
			assert mParallelCompositions.values().stream()
					.noneMatch(s -> s.contains(edge)) : "Intermediate edge should not be used in parallel composition";

			mSequentialCompositions.remove(edge);
			mParallelCompositions.remove(edge);
		}
		mIntermediateEdges.clear();
	}

	private void printMapping(final IIcfgTransition<IcfgLocation> newEdge,
			final List<IIcfgTransition<IcfgLocation>> originalEdges) {
		mLogger.info(
				markCodeblock(newEdge) + newEdge.hashCode() + " is mapped to " + getCollectionString(originalEdges));
	}

	private void printMapping(final IIcfgTransition<IcfgLocation> newEdge,
			final Set<IIcfgTransition<IcfgLocation>> originalEdges) {
		mLogger.info(markCodeblock(newEdge) + newEdge.hashCode() + " is mapped (in parallel) to "
				+ getCollectionString(originalEdges));
	}

	private static String getCollectionString(final Collection<IIcfgTransition<IcfgLocation>> originalEdges) {
		return originalEdges.stream().map(a -> markCodeblock(a) + String.valueOf(a.hashCode()))
				.collect(Collectors.joining(","));
	}

	public void addAteTransformer(final IIcfgTransition<IcfgLocation> newEdge,
			final Consumer<AtomicTraceElementBuilder<IIcfgTransition<IcfgLocation>>> transformer) {
		mAteTransformer.merge(newEdge, transformer, Consumer::andThen);
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
		for (final Entry<IIcfgTransition<IcfgLocation>, List<IIcfgTransition<IcfgLocation>>> entry : mSequentialCompositions
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
		mLogger.fatal(
				new ProgramExecutionFormatter<>(new IcfgBacktranslationValueProvider<IIcfgTransition<IcfgLocation>>())
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
		return new ProgramState<>(variable2Values, getTargetExpressionClass());
	}

	public void setVariableBlacklist(final Set<Term> variableBlacklist) {
		mVariableBlacklist = variableBlacklist;
	}

}
