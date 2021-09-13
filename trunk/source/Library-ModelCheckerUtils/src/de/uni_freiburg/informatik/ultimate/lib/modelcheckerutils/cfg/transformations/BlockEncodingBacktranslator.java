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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.translation.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.ProgramExecutionFormatter;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.AtomicTraceElementBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.BranchEncoderRenaming;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class BlockEncodingBacktranslator<L extends IAction>
		extends DefaultTranslator<L, L, Term, Term, IcfgLocation, IcfgLocation> {

	private static final boolean PRINT_MAPPINGS = false;

	private final Map<L, List<L>> mSequentialCompositions = new HashMap<>();

	// For each sequential compositions, stores renamings applied to branch encoders (or null if there are none). Such
	// renaming may be necessary when sequentially composing transitions that share branch encoders.
	private final Map<L, List<BranchEncoderRenaming>> mBranchEncoderRenamings = new HashMap<>();

	private final Map<L, Set<L>> mParallelCompositions = new HashMap<>();

	private final Map<L, TermVariable> mBranchEncoderMapping = new HashMap<>();

	private final Map<L, Consumer<AtomicTraceElementBuilder<L>>> mAteTransformer = new HashMap<>();

	private final Map<IcfgLocation, IcfgLocation> mLocationMapping = new HashMap<>();
	private final ILogger mLogger;
	private final Set<L> mIntermediateEdges = new HashSet<>();
	/**
	 * Function that determines how expression (here {@link Term}s) are translated. By default we use the identity.
	 */
	private Function<Term, Term> mTermTranslator = (x -> x);
	/**
	 * Set of variables that are removed from {@link ProgramState}s. By default we use the empty set. (This can be
	 * helpful for auxiliary variables that we cannot translate).
	 */
	private Set<Term> mVariableBlacklist = Collections.emptySet();

	public BlockEncodingBacktranslator(final Class<? extends L> traceElementType, final Class<Term> expressionType,
			final ILogger logger) {
		super(traceElementType, traceElementType, expressionType, expressionType);
		mLogger = logger;
	}

	@SuppressWarnings("unchecked")
	@Override
	public IProgramExecution<L, Term> translateProgramExecution(final IProgramExecution<L, Term> oldPe) {
		if (oldPe == null) {
			throw new IllegalArgumentException("programExecution is null");
		}

		if (!(oldPe instanceof IcfgProgramExecution)) {
			throw new IllegalArgumentException("argument is not IcfgProgramExecution but " + oldPe.getClass());

		}
		final IcfgProgramExecution<L> oldIcfgPe = ((IcfgProgramExecution<L>) oldPe);
		final Map<TermVariable, Boolean>[] oldBranchEncoders = oldIcfgPe.getBranchEncoders();
		assert oldBranchEncoders.length == oldIcfgPe.getLength() : "wrong branchencoders";
		assert checkCallStackSourceProgramExecution(mLogger,
				oldIcfgPe) : "callstack of initial program execution already broken";

		final List<AtomicTraceElement<L>> newTrace = new ArrayList<>();
		final List<ProgramState<Term>> newValues = new ArrayList<>();
		final List<Map<TermVariable, Boolean>> newBranchEncoders = new ArrayList<>();

		if (PRINT_MAPPINGS) {
			mLogger.info("Using the following mapping");
			for (final Entry<L, List<L>> entry : mSequentialCompositions.entrySet()) {
				printMapping(entry.getKey(), entry.getValue());
			}
		}

		for (int i = 0; i < oldIcfgPe.getLength(); ++i) {
			final AtomicTraceElement<L> currentATE = oldIcfgPe.getTraceElement(i);
			final var mappedEdges = translateBack(currentATE.getTraceElement(), oldBranchEncoders[i]);

			final var iter = mappedEdges.iterator();
			while (iter.hasNext()) {
				final var current = iter.next();
				final L currentEdge = current.getFirst();
				final Map<TermVariable, Boolean> currentBE = current.getSecond();

				final AtomicTraceElementBuilder<L> builder =
						AtomicTraceElementBuilder.fromReplaceElementAndStep(currentATE, currentEdge);
				final var transformer = mAteTransformer.get(currentATE.getTraceElement());
				if (transformer != null) {
					transformer.accept(builder);
				}
				newTrace.add(builder.build());

				newBranchEncoders.add(currentBE);
				if (iter.hasNext()) {
					newValues.add(null);
				}
			}
			final ProgramState<Term> newProgramState = translateProgramState(oldIcfgPe.getProgramState(i));
			newValues.add(newProgramState);
		}

		final Map<Integer, ProgramState<Term>> newValuesMap = new HashMap<>();
		newValuesMap.put(-1, oldIcfgPe.getInitialProgramState());
		for (int i = 0; i < newValues.size(); ++i) {
			newValuesMap.put(i, newValues.get(i));
		}

		final IcfgProgramExecution<L> newPe = new IcfgProgramExecution<>(newTrace, newValuesMap,
				newBranchEncoders.toArray(new Map[newBranchEncoders.size()]), oldIcfgPe.isConcurrent(),
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
	private Collection<Pair<L, Map<TermVariable, Boolean>>> translateBack(final L transition,
			final Map<TermVariable, Boolean> branchEncoders) {
		final ArrayDeque<Pair<L, Map<TermVariable, Boolean>>> result = new ArrayDeque<>();

		final ArrayDeque<L> stack = new ArrayDeque<>();
		final ArrayDeque<Map<TermVariable, Boolean>> branchEncoderStack = new ArrayDeque<>();
		stack.push(transition);
		branchEncoderStack.push(branchEncoders == null ? Map.of() : branchEncoders);

		while (!stack.isEmpty()) {
			final L current = stack.pop();
			final Map<TermVariable, Boolean> currentBE = branchEncoderStack.pop();

			if (mSequentialCompositions.containsKey(current)) {
				final List<L> sequence = mSequentialCompositions.get(current);
				assert sequence != null;

				final List<BranchEncoderRenaming> renamings = mBranchEncoderRenamings.get(current);
				assert renamings != null && renamings.size() == sequence.size() : "missing branch encoder information";

				// Put the transitions making up this composition on the stack.
				// Last transition in the sequence is on top.
				int i = 0;
				for (final L component : sequence) {
					stack.push(component);

					final BranchEncoderRenaming renaming = renamings.get(i);
					branchEncoderStack.push(renaming == null ? currentBE : renaming.applyToValues(currentBE));
					i++;
				}
			} else if (mParallelCompositions.containsKey(current)) {
				final Set<L> choices = mParallelCompositions.get(current);
				assert choices != null;

				if (currentBE == null) {
					mLogger.warn("Failed to translate choice composition: Branch encoders not available.");
					result.addFirst(new Pair<>(current, currentBE));
					continue;
				}

				boolean choiceFound = false;
				for (final L choice : choices) {
					assert mBranchEncoderMapping.get(choice) != null : "Choice composition is missing branch encoder";
					final TermVariable indicator = mBranchEncoderMapping.get(choice);
					assert currentBE.get(indicator) != null : "Branch indicator value was unknown: " + indicator
							+ " in " + currentBE;
					if (currentBE.get(indicator)) {
						stack.push(choice);
						branchEncoderStack.push(currentBE);
						choiceFound = true;
						break;
					}
				}
				assert choiceFound : "Could not determine correct choice for choice composition";
			} else {
				// Transition is assumed to be original.
				// As the last transition of a sequence is handled first (top of stack, see
				// above), we must prepend this transition to the result (instead of appending).
				result.addFirst(new Pair<>(current, currentBE));
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
	public void mapEdges(final L newEdge, final L originalEdge) {
		mapEdges(newEdge, originalEdge, (BranchEncoderRenaming) null);
	}

	/**
	 * Maps edges composed with sequential composition to the original edges.
	 *
	 * @param newEdge
	 *            The sequential composition
	 * @param originalEdge
	 *            The original edge involved in the composition
	 * @param branchEncoderRenaming
	 *            Branch encoder renaming applied at this position in the sequential composition; or null if no such
	 *            renaming occurred.
	 */
	public void mapEdges(final L newEdge, final L originalEdge, final BranchEncoderRenaming branchEncoderRenaming) {
		final List<L> limboEdges = mSequentialCompositions.get(originalEdge);
		if (limboEdges != null) {
			// an intermediate edge is replaced by a new edge
			mIntermediateEdges.add(originalEdge);

			final var limboRenamings = mBranchEncoderRenamings.get(originalEdge);

			int i = 0;
			for (final L limboEdge : limboEdges) {
				mapEdges(newEdge, limboEdge,
						BranchEncoderRenaming.compose(branchEncoderRenaming, limboRenamings.get(i)));
				i++;
			}
			return;
		}

		final List<L> originalEdges = mSequentialCompositions.computeIfAbsent(newEdge, x -> new ArrayList<>());
		originalEdges.add(originalEdge);
		mBranchEncoderRenamings.computeIfAbsent(newEdge, x -> new ArrayList<>()).add(branchEncoderRenaming);

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
	public void mapEdges(final L newEdge, final Map<TermVariable, L> originalEdges) {

		for (final Map.Entry<TermVariable, L> entry : originalEdges.entrySet()) {
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
	public void mapEdges(final L newEdge, final L originalEdge, final TermVariable branchEncoder) {
		final TermVariable oldEncoder = mBranchEncoderMapping.get(originalEdge);
		assert oldEncoder == null || oldEncoder == branchEncoder : "Ambiguous branch encoder for transition";
		mBranchEncoderMapping.put(originalEdge, branchEncoder);

		final Set<L> limboEdges = mParallelCompositions.get(originalEdge);
		if (limboEdges != null) {
			mIntermediateEdges.add(originalEdge);
			for (final L limboEdge : limboEdges) {
				mapEdges(newEdge, limboEdge, mBranchEncoderMapping.get(limboEdge));
			}
			return;
		}

		final Set<L> originalEdges = mParallelCompositions.computeIfAbsent(newEdge, x -> new HashSet<>());
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
		for (final L edge : mIntermediateEdges) {
			assert mSequentialCompositions.values().stream().noneMatch(
					s -> s.contains(edge)) : "Intermediate edge should not be used in sequential composition";
			assert mParallelCompositions.values().stream()
					.noneMatch(s -> s.contains(edge)) : "Intermediate edge should not be used in parallel composition";

			mSequentialCompositions.remove(edge);
			mParallelCompositions.remove(edge);
		}
		mIntermediateEdges.clear();
	}

	private void printMapping(final L newEdge, final List<L> originalEdges) {
		mLogger.info(
				markCodeblock(newEdge) + newEdge.hashCode() + " is mapped to " + getCollectionString(originalEdges));
	}

	private void printMapping(final L newEdge, final Set<L> originalEdges) {
		mLogger.info(markCodeblock(newEdge) + newEdge.hashCode() + " is mapped (in parallel) to "
				+ getCollectionString(originalEdges));
	}

	private static <L extends IAction> String getCollectionString(final Collection<L> originalEdges) {
		return originalEdges.stream().map(a -> markCodeblock(a) + String.valueOf(a.hashCode()))
				.collect(Collectors.joining(","));
	}

	public void addAteTransformer(final L newEdge, final Consumer<AtomicTraceElementBuilder<L>> transformer) {
		mAteTransformer.merge(newEdge, transformer, Consumer::andThen);
	}

	private static <L extends IAction> String markCodeblock(final L newEdge) {
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
	public Map<L, L> getEdgeMapping() {
		final Map<L, L> rtr = new HashMap<>();
		for (final Entry<L, List<L>> entry : mSequentialCompositions.entrySet()) {
			if (entry.getValue().size() > 1) {
				throw new UnsupportedOperationException(
						"The new edge " + entry.getKey() + " is mapped to multiple edges");
			}
			rtr.put(entry.getKey(), entry.getValue().isEmpty() ? null : entry.getValue().get(0));
		}
		return rtr;
	}

	@Override
	protected void printBrokenCallStackSource(final List<AtomicTraceElement<L>> trace, final int breakpointIndex) {
		final List<L> teList = trace.stream().limit(breakpointIndex).map(AtomicTraceElement::getTraceElement)
				.collect(Collectors.toList());
		mLogger.fatal(new ProgramExecutionFormatter<>(new IcfgBacktranslationValueProvider<L>())
				.formatProgramExecution(IcfgProgramExecution.create(teList, Collections.emptyMap())));
	}

	@Override
	protected void printBrokenCallStackTarget(final List<AtomicTraceElement<L>> trace, final int breakpointIndex) {
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
