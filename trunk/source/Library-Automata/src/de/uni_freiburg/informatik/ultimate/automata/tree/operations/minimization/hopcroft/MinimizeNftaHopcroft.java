/*
 * Copyright (C) 2014-2017 Daniel Tischner <zabuza.dev@gmail.com>
 * Copyright (C) 2009-2017 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.tree.operations.minimization.hopcroft;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.StringRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.minimization.performance.SinkMergeIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ToolchainStorage;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Operation that minimizes non-deterministic finite bottom-up tree automata
 * (NFTA-BU) by using a modified variant of the Hopcroft algorithm. The
 * resulting automaton is a minimal automaton that is bisimulation-equivalent to
 * the input.<br/>
 * Runtime is in:<br/>
 * <b>O(?)</b> with usage of<br/>
 * <b>O(?)</b> space<br/>
 * where 'r' is the maximum rank of the input alphabet, 'n' is the number of
 * states and 'm' the number of rules.<br/>
 * <br/>
 * The algorithm follows the outline given in [1] and improves the
 * implementation by using some techniques described in [2]:<br/>
 * <ol>
 * <li><i>2016 Bjorklund, Johanna et al. - A taxonomy of minimisation algorithms
 * for deterministic tree automata.</i></li>
 * <li><i>2006 Abdulla, Parosh Aziz et al. - Bisimulation Minimization of Tree
 * Automata.</i></li>
 * </ol>
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 * @param <LETTER>
 *            The class for letters of the tree automaton
 * @param <STATE>
 *            The class for states of the tree automaton
 */
public final class MinimizeNftaHopcroft<LETTER extends IRankedLetter, STATE>
		extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> {

	/**
	 * Demo usage of the operation. Also used for debugging purpose.
	 * 
	 * @param args
	 *            Not supported
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public static void main(final String[] args) throws AutomataOperationCanceledException {
		// Dummy services
		final AutomataLibraryServices services = new AutomataLibraryServices(new ToolchainStorage());
		final StringFactory mergeFactory = new StringFactory();

		// Build example tree automaton from whiteboard
		final TreeAutomatonBU<StringRankedLetter, String> tree = new TreeAutomatonBU<>();
		// States
		final String q1 = "q1";
		final String q2 = "q2";
		final String q3 = "q3";
		final String q4 = "q4";
		final String q5 = "q5";
		final String q6 = "q6";
		final String q7 = "q7";
		tree.addState(q1);
		tree.addState(q2);
		tree.addState(q3);
		tree.addState(q4);
		tree.addState(q7);
		tree.addFinalState(q5);
		tree.addFinalState(q6);

		// Letter
		final StringRankedLetter aLetter = new StringRankedLetter("a", 0);
		final StringRankedLetter gLetter = new StringRankedLetter("g", 1);
		final StringRankedLetter fLetter = new StringRankedLetter("f", 2);
		tree.addLetter(aLetter);
		tree.addLetter(fLetter);
		tree.addLetter(gLetter);

		// Rules
		tree.addRule(new TreeAutomatonRule<>(aLetter, Collections.emptyList(), q1));
		tree.addRule(new TreeAutomatonRule<>(aLetter, Collections.emptyList(), q2));
		tree.addRule(new TreeAutomatonRule<>(aLetter, Collections.emptyList(), q3));
		tree.addRule(new TreeAutomatonRule<>(aLetter, Collections.emptyList(), q4));
		tree.addRule(new TreeAutomatonRule<>(gLetter, Collections.singletonList(q3), q7));
		tree.addRule(new TreeAutomatonRule<>(fLetter, Arrays.asList(q1, q2), q5));
		tree.addRule(new TreeAutomatonRule<>(fLetter, Arrays.asList(q3, q4), q6));

		System.out.println("Tree before minimization: " + tree);

		final ITreeAutomatonBU<StringRankedLetter, String> result = new MinimizeNftaHopcroft<>(services, mergeFactory,
				tree).getResult();

		System.out.println();
		System.out.println("Tree after minimization: " + result);
	}

	/**
	 * Data-structure which maps compound progress blocks to a set of
	 * representatives of the blocks it contains. A compound progress block belongs
	 * to the <tt>progress relation</tt> and consists of several blocks of the
	 * current relation.
	 */
	private final LinkedHashMap<STATE, LinkedHashSet<STATE>> mCompoundBlocks;
	/**
	 * A boolean indicating if the input automaton has no final states. Used for a
	 * fast termination.
	 */
	private boolean mNoFinalStates;
	/**
	 * The operand tree automaton to minimize.
	 */
	private final ITreeAutomatonBU<LETTER, STATE> mOperand;
	/**
	 * The partition of all states which gets refined until it represents the final
	 * partition of bisimulation equivalent states.
	 */
	private UnionFind<STATE> mPartition;
	/**
	 * The partition of all states which iteratively approaches the regular
	 * partition. Once they are the same a fixed point has been reached which
	 * indicates that the partition represents a valid bisimulation.
	 */
	private final UnionFind<STATE> mProgressPartition;
	/**
	 * The resulting tree automaton after minimizing the operand.
	 */
	private ITreeAutomatonBU<LETTER, STATE> mResult;
	/**
	 * Factory used to create sink states, merge and intersect states.
	 */
	private final SinkMergeIntersectStateFactory<STATE> mSinkMergeIntersectFactory;

	/**
	 * Minimizes the given tree automaton operand. The result can be obtained by
	 * using {@link #getResult()}.
	 * 
	 * @param <SF>
	 *            Factory that is able to create sink states, merge and intersect
	 *            states
	 * 
	 * @param services
	 *            Ultimate services
	 * @param sinkMergeIntersectFactory
	 *            The factory to use for creating sink states, merge and intersect
	 *            states
	 * @param operand
	 *            The operand tree automaton to minimize
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE>> MinimizeNftaHopcroft(
			final AutomataLibraryServices services, final SF sinkMergeIntersectFactory,
			final ITreeAutomatonBU<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		super(services);
		// TODO Analyze complexity of algorithm (but improve it first)
		// The algorithm itself only needs a merge factory. However to proof correctness
		// (with enabled assertions) currently also sink and intersect factories are
		// needed.
		this.mSinkMergeIntersectFactory = new SinkMergeIntersectStateFactory<>(sinkMergeIntersectFactory,
				sinkMergeIntersectFactory, sinkMergeIntersectFactory);
		this.mOperand = operand;

		this.mResult = null;
		this.mCompoundBlocks = new LinkedHashMap<>();
		this.mProgressPartition = new UnionFind<>();
		this.mNoFinalStates = false;

		if (this.mLogger.isInfoEnabled()) {
			this.mLogger.info(startMessage());
		}

		this.mResult = doOperation();

		if (this.mLogger.isInfoEnabled()) {
			this.mLogger.info(exitMessage());
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.GeneralOperation#checkResult(de.
	 * uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory)
	 */
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// Check language equivalence between input and result automaton
		final IsEquivalent<LETTER, STATE> equivalenceCheck = new IsEquivalent<>(this.mServices,
				this.mSinkMergeIntersectFactory, this.mOperand, this.mResult);
		final boolean isEquivalent = equivalenceCheck.getResult().booleanValue();

		if (!isEquivalent && this.mLogger.isInfoEnabled()) {
			this.mLogger.info("Counterexample: " + equivalenceCheck.getCounterexample().get());
		}

		return isEquivalent;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#getResult()
	 */
	@Override
	public ITreeAutomatonBU<LETTER, STATE> getResult() {
		return this.mResult;
	}

	/**
	 * Builds a minimal tree automaton accepting the empty language. The automaton
	 * consists of no states, no letters and no rules, it is empty.
	 * 
	 * @return A minimal tree automaton accepting the empty language
	 */
	private ITreeAutomatonBU<LETTER, STATE> buildEmptyLanguageTree() {
		return new TreeAutomatonBU<>();
	}

	/**
	 * Collects information of how states behave under rules with a destination
	 * inside the given block. This information is called context.<br>
	 * A context represents similar, with respect to the current partition, rules
	 * and holds which states are able to use that rule at given positions. Based on
	 * that splits can be determined since if a state is able to use a rule but
	 * others of the same block are not, then they must not stay in the same block.
	 * 
	 * @param destinationBlock
	 *            The block used as destination for rules to be selected
	 * @return An iterator over all collected contexts
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private Iterator<RuleContext<LETTER, STATE>> collectContexts(final Set<STATE> destinationBlock)
			throws AutomataOperationCanceledException {
		// We now consider all rules that lead to a state contained in the current
		// selected block. With context objects we determine differences between the
		// behavior of states that are currently in the same block of the regular
		// partition.
		// A context is a more general rule representing several concrete
		// rules. Therefore a context does not have states as source and destination but
		// blocks of states. Additionally it remembers which states occurred in concrete
		// rules at given positions in the source-tuple. By that we are able to find
		// states in the same block that have a different behavior which then need to be
		// split in the next step of the algorithm.

		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Starting to collect contexts");
		}
		final STATE destinationRepresentative = this.mPartition.find(destinationBlock.iterator().next());
		final NestedMap2<LETTER, List<STATE>, RuleContext<LETTER, STATE>> letterAndSourceSignatureToContexts = new NestedMap2<>();

		// Find all rules whose destination is in the given block
		for (final STATE destination : destinationBlock) {
			final Map<LETTER, Iterable<List<STATE>>> predecessors = this.mOperand.getPredecessors(destination);
			for (final LETTER letter : predecessors.keySet()) {
				// Skip all 0-ranked letters as they do not contribute to the language directly
				if (letter.getRank() == 0) {
					continue;
				}

				final Iterable<List<STATE>> sources = predecessors.get(letter);
				for (final List<STATE> source : sources) {
					// At this point the rule is fully characterized with a source-tuple,
					// a letter and a destination
					if (this.mLogger.isDebugEnabled()) {
						this.mLogger.debug("Looking at rule: " + source + " -" + letter + "-> " + destination);
					}
					// Build the signature of this source
					final List<STATE> signature = new ArrayList<>(source.size());
					for (final STATE stateAtPosition : source) {
						final STATE representative = this.mPartition.find(stateAtPosition);
						signature.add(representative);
					}

					// Find the context under this signature
					RuleContext<LETTER, STATE> context = letterAndSourceSignatureToContexts.get(letter, signature);
					if (context == null) {
						context = new RuleContext<>(signature, letter, destinationRepresentative);
						letterAndSourceSignatureToContexts.put(letter, signature, context);
					}

					// Add the current rule to the corresponding context
					context.addSource(source);

					if (this.mLogger.isDebugEnabled()) {
						this.mLogger.debug("Added rule to context: " + context);
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (this.mServices.getProgressAwareTimer() != null && isCancellationRequested()) {
						this.mLogger.debug("Stopped at collecting contexts");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}
			}
		}

		return letterAndSourceSignatureToContexts.values().iterator();
	}

	/**
	 * Executes this operation.
	 * 
	 * @return The resulting tree automaton obtained after minimizing the operand.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private ITreeAutomatonBU<LETTER, STATE> doOperation() throws AutomataOperationCanceledException {
		// We construct two relations, one regular and one progress relation. In each
		// round we refine the regular relation based on how states behave under
		// different rules. Also, in each round the progress relation overtakes one
		// block of the partition represented by the regular relation. The algorithm
		// terminates once the regular and the progress relation are equal. Besides that
		// the progress relation is used to be able to quickly select compound blocks
		// and the method to always just overtake one block in each round ensures that
		// really each rule is considered.
		initPartition();

		// If there are no final states abort since the language is empty
		if (this.mNoFinalStates) {
			return buildEmptyLanguageTree();
		}

		// Continue the refinement of the partition until there is no compound progress
		// block anymore. At this point the progress relation has become the same then
		// the current iteration, i.e. there is no further refinement possible and a
		// fixed point has been reached which represents a valid bisimulation.
		boolean initialRound = true;
		while (!this.mCompoundBlocks.isEmpty()) {
			if (this.mLogger.isDebugEnabled()) {
				this.mLogger.debug("Starting round");
			}
			final STATE representativeOfBlock = selectBlockForRound(initialRound);
			// In the paper this block is often referred to as B
			final Set<STATE> block = this.mPartition.getContainingSet(representativeOfBlock);

			final Iterator<RuleContext<LETTER, STATE>> contexts = collectContexts(block);
			refineBasedOnContexts(contexts, block);

			// Preparations for the next round
			if (initialRound) {
				initialRound = false;
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (this.mServices.getProgressAwareTimer() != null && isCancellationRequested()) {
				this.mLogger.debug("Stopped at end of round");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}

		// Merge the automaton using the current refined partition
		return mergeUsingPartition(this.mPartition);
	}

	/**
	 * Builds and sets the initial partition and relation which separates final from
	 * non-final states.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private void initPartition() throws AutomataOperationCanceledException {
		// The initial partition of the regular relation consists of two blocks, all
		// final states and all non-final states. The initial progress relation only has
		// one block containing all states. By that the we have one compound progress
		// block containing both blocks of the regular relation.
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Creating initial partition");
		}

		final Set<STATE> finalBlock = new HashSet<>();
		final Set<STATE> nonFinalBlock = new HashSet<>();

		// Iterate all states and put them in the corresponding block
		for (final STATE state : this.mOperand.getStates()) {
			if (this.mOperand.isFinalState(state)) {
				finalBlock.add(state);
			} else {
				nonFinalBlock.add(state);
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (this.mServices.getProgressAwareTimer() != null && isCancellationRequested()) {
				this.mLogger.debug("Stopped at creating initial partition/block creation");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}

		if (finalBlock.isEmpty()) {
			if (this.mLogger.isDebugEnabled()) {
				this.mLogger.debug("There are no final states, returning");
			}
			this.mNoFinalStates = true;
			return;
		}

		// Setup the initial partition
		this.mPartition = new UnionFind<>();
		this.mPartition.addEquivalenceClass(finalBlock);
		this.mPartition.addEquivalenceClass(nonFinalBlock);
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Initial partition is: " + this.mPartition);
		}

		// Build the progress partition which initially holds all states in one block
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Creating initial progress partition");
		}
		this.mProgressPartition.addEquivalenceClass(this.mOperand.getStates());
		final STATE representativeOfProgressBlock = this.mProgressPartition.getAllRepresentatives().stream().findFirst()
				.get();
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Initial progress partition is: " + this.mProgressPartition);
		}

		// Register the compound block
		final LinkedHashSet<STATE> representativesOfCompoundBlocks = new LinkedHashSet<>();
		for (final STATE representative : this.mPartition.getAllRepresentatives()) {
			// Initially all blocks belong to the only compound progress block
			// which consists of all states
			representativesOfCompoundBlocks.add(representative);
		}
		this.mCompoundBlocks.put(representativeOfProgressBlock, representativesOfCompoundBlocks);
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Initial compound blocks are: " + this.mCompoundBlocks);
		}
	}

	/**
	 * Merges the operand by using the given partition. The resulting automaton
	 * contains a state for every block in the given partition. Thus every states
	 * and rule of the operand will result in a representative where every
	 * occurrence of states are replaced by the corresponding merged state.
	 * 
	 * @param partition
	 *            The partition to use for merge
	 * @return The merged automaton
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private ITreeAutomatonBU<LETTER, STATE> mergeUsingPartition(final UnionFind<STATE> partition)
			throws AutomataOperationCanceledException {
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Starting to construct the result");
		}
		final HashMap<STATE, STATE> representativeToMergedState = new HashMap<>();
		final TreeAutomatonBU<LETTER, STATE> result = new TreeAutomatonBU<>();

		// Add resulting states
		for (final STATE representative : partition.getAllRepresentatives()) {
			final Set<STATE> block = partition.getEquivalenceClassMembers(representative);

			// Merge the states of the block
			final STATE mergedState = this.mSinkMergeIntersectFactory.merge(block);
			if (this.mLogger.isDebugEnabled()) {
				this.mLogger.debug("Merged " + block + " to " + mergedState);
			}
			representativeToMergedState.put(representative, mergedState);
			if (this.mOperand.isFinalState(representative)) {
				result.addFinalState(mergedState);
			} else {
				result.addState(mergedState);
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (this.mServices.getProgressAwareTimer() != null && isCancellationRequested()) {
				this.mLogger.debug("Stopped at creating result/merging states");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}

		// Add resulting letters
		for (final LETTER letter : this.mOperand.getAlphabet()) {
			result.addLetter(letter);
			if (this.mLogger.isDebugEnabled()) {
				this.mLogger.debug("Added letter: " + letter);
			}
		}

		// Add resulting rules
		for (final TreeAutomatonRule<LETTER, STATE> rule : this.mOperand.getRules()) {
			// Merge source
			final List<STATE> source = rule.getSource();
			final List<STATE> mergedSource = new ArrayList<>(source.size());
			for (final STATE state : source) {
				final STATE mergedState = representativeToMergedState.get(partition.find(state));
				mergedSource.add(mergedState);
			}

			// Merge destination
			final STATE mergedDestination = representativeToMergedState.get(partition.find(rule.getDest()));

			// Add the merged rule
			final TreeAutomatonRule<LETTER, STATE> mergedRule = new TreeAutomatonRule<>(rule.getLetter(), mergedSource,
					mergedDestination);
			result.addRule(mergedRule);

			if (this.mLogger.isDebugEnabled()) {
				this.mLogger.debug("Merged rule=" + rule + " to mergedRule=" + mergedRule);
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (this.mServices.getProgressAwareTimer() != null && isCancellationRequested()) {
				this.mLogger.debug("Stopped at creating result/adding rules");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}

		return result;
	}

	/**
	 * Refines the current partition based on the given contexts.<br>
	 * A context represents similar, with respect to the current partition, rules
	 * and holds which states are able to use that rule at given positions. Based on
	 * that splits can be determined since if a state is able to use a rule but
	 * others of the same block are not, then they must not stay in the same block.
	 * 
	 * @param contexts
	 *            The contexts to refine based on
	 * @param destinationBlock
	 *            The block used as destination all rules in the contexts
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private void refineBasedOnContexts(final Iterator<RuleContext<LETTER, STATE>> contexts,
			final Set<STATE> destinationBlock) throws AutomataOperationCanceledException {
		// Based on the previously collected context objects we now find differences in
		// the behavior of states that are currently in the same block of the regular
		// relation. States that are listed in the same block but behave differently
		// need to get separated.
		// Therefore we iterate all contexts and all positions in their source-tuple.
		// If, for example, such a position corresponds to states of a block A = {1, 2,
		// 3} but the context only lists the states {1, 2} as possible states of
		// concrete rules, the symmetric pairs (1, 3) and (2, 3) need to get removed
		// from the regular relation since state 3 behaves differently as states 1 and
		// 2, based on the definition of bisimulation.

		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Starting to refine based on contexts");
		}

		// Iterate all contexts and refine the partition. In the paper this method is
		// often referred to as 'split'
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Starting to refine partition");
			this.mLogger.debug("Partition before update is: " + this.mPartition);
		}
		UnionFind<STATE> refinedPartition = null;
		while (contexts.hasNext()) {
			final RuleContext<LETTER, STATE> context = contexts.next();

			if (this.mLogger.isDebugEnabled()) {
				this.mLogger.debug("Looking at context: " + context);
			}
			// Iterate each position
			for (int i = 0; i < context.getSourceSize(); i++) {
				// If operation was canceled, for example from the
				// Ultimate framework
				if (this.mServices.getProgressAwareTimer() != null && isCancellationRequested()) {
					this.mLogger.debug("Stopped at refining based on contexts/refining relation");
					throw new AutomataOperationCanceledException(this.getClass());
				}

				final Set<STATE> sourceStatesAtPosition = context.getSourceStatesAtPosition(i);
				final STATE representative = context.getSourceRepresentativeAtPosition(i);
				final Set<STATE> block = this.mPartition.getContainingSet(representative);

				if (this.mLogger.isDebugEnabled()) {
					final Set<STATE> statesNotAtPosition = new HashSet<>(block.size() - sourceStatesAtPosition.size());
					for (final STATE stateOfBlock : block) {
						if (!sourceStatesAtPosition.contains(stateOfBlock)) {
							statesNotAtPosition.add(stateOfBlock);
						}
					}
					this.mLogger.debug("At position " + i + " statesAt=" + sourceStatesAtPosition + ", statesNotAt="
							+ statesNotAtPosition);
				}

				// Whether this position yields changes
				if (sourceStatesAtPosition.size() == block.size()) {
					if (this.mLogger.isDebugEnabled()) {
						this.mLogger.debug("Source position does not yield changes");
					}
					continue;
				}

				if (refinedPartition == null) {
					// Create a clone to iteratively refine
					refinedPartition = this.mPartition.clone();
				}

				// Find all refined equivalence classes of the current refinement which belong
				// to the corresponding block
				final Set<STATE> refinedBlockRepresentatives = new HashSet<>();
				for (final STATE state : block) {
					final STATE refinedRepresentative = refinedPartition.find(state);
					refinedBlockRepresentatives.add(refinedRepresentative);
				}

				// Compute the intersection of the current partition with the partition
				// represented by the states at and the states not at this source position.
				for (final STATE refinedRepresentative : refinedBlockRepresentatives) {
					final Set<STATE> refinedBlock = refinedPartition.getContainingSet(refinedRepresentative);

					final HashSet<STATE> refinedStatesAtSourcePosition = new HashSet<>();
					final HashSet<STATE> refinedStatesNotAtSourcePosition = new HashSet<>();
					for (final STATE stateOfRefinedBlock : refinedBlock) {
						if (sourceStatesAtPosition.contains(stateOfRefinedBlock)) {
							refinedStatesAtSourcePosition.add(stateOfRefinedBlock);
						} else {
							refinedStatesNotAtSourcePosition.add(stateOfRefinedBlock);
						}
					}

					// Whether the block is to be split
					if (refinedStatesAtSourcePosition.isEmpty() || refinedStatesNotAtSourcePosition.isEmpty()) {
						continue;
					}

					// Split the block by removing and re-adding
					refinedPartition.removeAll(refinedBlock);
					refinedPartition.addEquivalenceClass(refinedStatesAtSourcePosition);
					refinedPartition.addEquivalenceClass(refinedStatesNotAtSourcePosition);

					if (this.mLogger.isDebugEnabled()) {
						this.mLogger.debug("Split block into: " + refinedStatesAtSourcePosition + " and "
								+ refinedStatesNotAtSourcePosition);
					}
				}
			}
		}
		// If there where changes update the partition by using the refined partition
		if (refinedPartition != null) {
			this.mPartition = refinedPartition;
		} else {
			if (this.mLogger.isDebugEnabled()) {
				this.mLogger.debug("Contexts did not yield any changes, partition was not refined");
			}
		}
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Partition after update is: " + this.mPartition);
		}

		// If operation was canceled, for example from the
		// Ultimate framework
		if (this.mServices.getProgressAwareTimer() != null && isCancellationRequested()) {
			this.mLogger.debug("Stopped at refining based on contexts/after updating partition");
			throw new AutomataOperationCanceledException(this.getClass());
		}

		// Update the compound progress blocks and split the block of the
		// current round off. Note that this step also needs to be done if no changes
		// where made, else we would not progress as we need to split the current block
		// from the progress partition in each round.
		updateCompoundBlocksAndProgressPartition(destinationBlock);
	}

	/**
	 * Selects a block that is used as starting point for splits in the next round.
	 * Splits are determined based on rules. In an iteration only rules that have
	 * states in this selected block will be selected. The selected block is part of
	 * a compound progress block and its size is less than the half of its
	 * containing progress block.<br>
	 * <br>
	 * If it is the initial round the method will always select the block of final
	 * states as all recognized words of the language must end with a final state.
	 * 
	 * @param initialRound
	 *            If it is the initial round, thus the block of final states should
	 *            be selected, or not.
	 * 
	 * @return A block used as starting point for splits
	 */
	private STATE selectBlockForRound(final boolean initialRound) {
		// The goal here is to find a block B of the relation and a block S of the
		// progress relation such that B belongs to S and |B| <= |S|/2. We find them by
		// memorizing compound progress blocks. That are blocks of the progress relation
		// which contain multiple blocks of the regular relation. Obviously all
		// choosable blocks B belong to such compound progress blocks.
		// However in the initial round we will always select the block of final states
		// since words contributing to the language always end there.
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Selecting a compound block for this round");
		}

		// Select a compound progress block. In the paper this block is often referred
		// to as S
		final LinkedHashSet<STATE> progressBlock = this.mCompoundBlocks.values().stream().findFirst().get();

		if (initialRound) {
			if (this.mLogger.isDebugEnabled()) {
				this.mLogger.debug("Round is initial");
			}
			// Find the representative of the block of final states as in the initial round
			// we always start with the set of final states
			for (final STATE representative : progressBlock) {
				// Could be done slightly faster by memorizing it before. However there are only
				// two representatives in the initial round thus it has no impact on
				// performance.
				if (this.mOperand.isFinalState(representative)) {
					return representative;
				}
			}
			throw new AssertionError("There is no final state in the initial progress block.");
		}

		// Select the block that is smaller than the half of the progress block. This is
		// ensured by selecting the smaller of two blocks.
		final Iterator<STATE> blockRepresentatives = progressBlock.iterator();
		final STATE firstRepresentative = blockRepresentatives.next();
		final STATE secondRepresentative = blockRepresentatives.next();

		// Select the smaller block of both
		final int firstBlockSize = this.mPartition.getContainingSet(firstRepresentative).size();
		final int secondBlockSize = this.mPartition.getContainingSet(secondRepresentative).size();
		if (firstBlockSize < secondBlockSize) {
			if (this.mLogger.isDebugEnabled()) {
				this.mLogger
						.debug("Block of " + firstRepresentative + " is smaller than block of " + secondRepresentative);
			}
			return firstRepresentative;
		}
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Block of " + secondRepresentative + " is smaller than block of " + firstRepresentative);
		}
		return secondRepresentative;
	}

	/**
	 * Updates the data about compound progress blocks by using the current
	 * partition. Also splits a given block from the current progress block. This is
	 * done such that in each round exactly one block is took over from the
	 * partition. If the partition does not change anymore the progress blocks will
	 * be equal to the partition after some steps. At this point a fixed point has
	 * reached and the partition represents a valid bisimulation.
	 * 
	 * @param blockToSplitOff
	 *            The block to split off
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private void updateCompoundBlocksAndProgressPartition(final Set<STATE> blockToSplitOff)
			throws AutomataOperationCanceledException {
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Starting to update compound blocks and progress partition");
		}
		// Split the given block off by making it its own equivalence class in the
		// progress partition. In the paper this method is often referred to as 'cut'.
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Progress partition before update is: " + this.mProgressPartition);
		}
		this.mProgressPartition.removeAll(blockToSplitOff);
		this.mProgressPartition.addEquivalenceClass(blockToSplitOff);
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Progress partition after update is: " + this.mProgressPartition);
		}

		// Determine compound progress blocks by registering all blocks under their
		// progress block
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Compound blocks before update are: " + this.mCompoundBlocks);
		}
		this.mCompoundBlocks.clear();
		// This map is used to determine when a progress block has more than one blocks,
		// i.e. when it is compound
		final HashMap<STATE, STATE> progressBlocksToFirstBlock = new HashMap<>();
		for (final STATE currentBlock : this.mPartition.getAllRepresentatives()) {
			// If operation was canceled, for example from the
			// Ultimate framework
			if (this.mServices.getProgressAwareTimer() != null && isCancellationRequested()) {
				this.mLogger.debug("Stopped at updating compound blocks");
				throw new AutomataOperationCanceledException(this.getClass());
			}
			if (this.mLogger.isDebugEnabled()) {
				this.mLogger.debug("Looking at partition block of " + currentBlock);
			}

			// Find the progress block this block belongs to
			final STATE progressBlock = this.mProgressPartition.find(currentBlock);

			final STATE firstBlock = progressBlocksToFirstBlock.get(progressBlock);
			if (firstBlock == null) {
				// It is the first block for this progress block. It is yet not decided whether
				// the progress block is compound.
				progressBlocksToFirstBlock.put(progressBlock, currentBlock);
				if (this.mLogger.isDebugEnabled()) {
					this.mLogger.debug("Block was first for progress block " + progressBlock);
				}
				continue;
			}

			// The progress block already has a block, it is compound
			LinkedHashSet<STATE> blocksBelongingToProgressBlock = this.mCompoundBlocks.get(progressBlock);
			if (blocksBelongingToProgressBlock == null) {
				// Create an entry and add the first registered block
				blocksBelongingToProgressBlock = new LinkedHashSet<>();
				blocksBelongingToProgressBlock.add(firstBlock);
				this.mCompoundBlocks.put(progressBlock, blocksBelongingToProgressBlock);
			}
			// Register the current block for this progress block
			blocksBelongingToProgressBlock.add(currentBlock);

			if (this.mLogger.isDebugEnabled()) {
				this.mLogger.debug("Progress block " + progressBlock + " is compound, currently is: "
						+ blocksBelongingToProgressBlock);
			}
		}
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Compound blocks after update are: " + this.mCompoundBlocks);
		}
	}

	/**
	 * Gets the operand of this operation.
	 * 
	 * @return The operand of this operation
	 */
	protected ITreeAutomatonBU<LETTER, STATE> getOperand() {
		return this.mOperand;
	}
}
