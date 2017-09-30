package de.uni_freiburg.informatik.ultimate.automata.tree.operations.minimization.hopcroft;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.SymmetricHashRelation;

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
	 * Constructs and returns a partition of elements that corresponds to the given
	 * symmetric relation. That means if the relation holds a pair <tt>(e1, e2)<tt>
	 * than elements <tt>e1<tt> and <tt>e2<tt> will be in the same block of the
	 * partition.
	 * 
	 * @param <E>
	 *            The class of the elements
	 * @param relation
	 *            The relation to construct the partition of
	 * @param allElements
	 *            A collection containing all elements to consider
	 * @return The partition of the elements corresponding to the given symmetric
	 *         relation
	 */
	private static <E> UnionFind<E> constructPartitionFromRelation(final SymmetricHashRelation<E> relation,
			final Collection<E> allElements) {
		final UnionFind<E> partition = new UnionFind<>();

		// Create the initial partition where every element is in its own block
		for (final E element : allElements) {
			partition.makeEquivalenceClass(element);
		}

		// Iterate the relation and union blocks corresponding to the pairs
		for (final Entry<E, E> pair : relation.entrySet()) {
			partition.union(pair.getKey(), pair.getValue());
		}

		return partition;
	}

	/**
	 * A set containing sets of representatives of compound blocks. A compound block
	 * belongs to the <tt>progress relation</tt> and consists of several blocks of
	 * the current relation.
	 */
	private final LinkedHashSet<LinkedHashSet<STATE>> mCompoundBlocks;
	/**
	 * Factory used to merge states.
	 */
	private final IMergeStateFactory<STATE> mMergeFactory;
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
	 * The relation of the current iteration which gets refined until it represents
	 * the final bisimulation equivalence relation.
	 */
	private final SymmetricHashRelation<STATE> mRelation;
	/**
	 * The resulting tree automaton after minimizing the operand.
	 */
	private ITreeAutomatonBU<LETTER, STATE> mResult;

	/**
	 * Minimizes the given tree automaton operand. The result can be obtained by
	 * using {@link #getResult()}.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param mergeFactory
	 *            The factory to use for merging states
	 * @param operand
	 *            The operand tree automaton to minimize
	 */
	public MinimizeNftaHopcroft(final AutomataLibraryServices services, final IMergeStateFactory<STATE> mergeFactory,
			final ITreeAutomatonBU<LETTER, STATE> operand) {
		super(services);

		// TODO Remove exception once finished
		final boolean operationNotYetImplemented = true;
		if (operationNotYetImplemented) {
			throw new UnsupportedOperationException("Not yet implemented");
		}

		this.mMergeFactory = mergeFactory;
		this.mOperand = operand;

		this.mResult = null;
		this.mRelation = new SymmetricHashRelation<>();
		this.mCompoundBlocks = new LinkedHashSet<>();
		this.mNoFinalStates = false;

		this.mResult = doOperation();
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
	 * @return A collection of all collected contexts
	 */
	private Collection<RuleContext<LETTER, STATE>> collectContexts(final Set<STATE> destinationBlock) {
		final STATE destinationRepresentative = this.mPartition.find(destinationBlock.iterator().next());
		final HashMap<List<STATE>, RuleContext<LETTER, STATE>> sourceSignatureToContexts = new HashMap<>();

		// Find all rules whose destination is in the given block
		for (final STATE destination : destinationBlock) {
			final Map<LETTER, Iterable<List<STATE>>> predecessors = this.mOperand.getPredecessors(destination);
			for (final LETTER letter : predecessors.keySet()) {
				final Iterable<List<STATE>> sources = predecessors.get(letter);
				for (final List<STATE> source : sources) {
					// At this point the rule is fully characterized with a source-tuple,
					// a letter and a destination
					// Build the signature of this source
					final List<STATE> signature = new ArrayList<>(source.size());
					for (final STATE stateAtPosition : source) {
						final STATE representative = this.mPartition.find(stateAtPosition);
						signature.add(representative);
					}

					// Find the context under this signature
					RuleContext<LETTER, STATE> context = sourceSignatureToContexts.get(signature);
					if (context == null) {
						context = new RuleContext<>(signature, letter, destinationRepresentative);
						sourceSignatureToContexts.put(signature, context);
					}

					// Add the current rule to the corresponding context
					context.addSource(source);
				}
			}
		}

		return sourceSignatureToContexts.values();
	}

	/**
	 * Executes this operation.
	 * 
	 * @return The resulting tree automaton obtained after minimizing the operand.
	 */
	private ITreeAutomatonBU<LETTER, STATE> doOperation() {
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
			final STATE representativeOfBlock = selectBlockForRound(initialRound);
			final Set<STATE> block = this.mPartition.getContainingSet(representativeOfBlock);

			final Collection<RuleContext<LETTER, STATE>> contexts = collectContexts(block);
			refineBasedOnContexts(contexts);

			// Preparations for the next round
			if (initialRound) {
				initialRound = false;
			}
		}

		// Merge the automaton using the current refined partition
		return mergeUsingPartition(this.mPartition);
	}

	/**
	 * Builds and sets the initial partition and relation which separates final from
	 * non-final states.
	 */
	private void initPartition() {
		final Set<STATE> finalBlock = new HashSet<>();
		final Set<STATE> nonFinalBlock = new HashSet<>();

		// Iterate all states and put them in the corresponding block
		for (final STATE state : this.mOperand.getStates()) {
			if (this.mOperand.isFinalState(state)) {
				finalBlock.add(state);
			} else {
				nonFinalBlock.add(state);
			}
		}

		if (finalBlock.isEmpty()) {
			this.mNoFinalStates = true;
			return;
		}

		// Setup the initial partition
		this.mPartition = new UnionFind<>();
		this.mPartition.addEquivalenceClass(finalBlock);
		this.mPartition.addEquivalenceClass(nonFinalBlock);
		final LinkedHashSet<STATE> representativesOfCompoundBlock = new LinkedHashSet<>();

		// Create the corresponding relation
		for (final STATE representative : this.mPartition.getAllRepresentatives()) {
			// Initially all blocks belong to the only compound block
			// which consists of all states
			representativesOfCompoundBlock.add(representative);

			for (final STATE otherBlockMembers : this.mPartition.getEquivalenceClassMembers(representative)) {
				// Skip if the other member is the representative
				if (otherBlockMembers.equals(representative)) {
					continue;
				}

				// Add the pair to the symmetric relation
				this.mRelation.addPair(representative, otherBlockMembers);
			}
		}
		// Build the transitive closure
		this.mRelation.makeTransitive();

		// Register the compound block
		this.mCompoundBlocks.add(representativesOfCompoundBlock);
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
	 */
	private ITreeAutomatonBU<LETTER, STATE> mergeUsingPartition(final UnionFind<STATE> partition) {
		final HashMap<STATE, STATE> representativeToMergedState = new HashMap<>();
		final TreeAutomatonBU<LETTER, STATE> result = new TreeAutomatonBU<>();

		// Add resulting states
		for (final STATE representative : partition.getAllRepresentatives()) {
			final Set<STATE> block = partition.getEquivalenceClassMembers(representative);

			// Merge the states of the block
			final STATE mergedState = this.mMergeFactory.merge(block);
			representativeToMergedState.put(representative, mergedState);
			if (this.mOperand.isFinalState(representative)) {
				result.addFinalState(mergedState);
			} else {
				result.addState(mergedState);
			}
		}

		// Add resulting letters
		for (final LETTER letter : this.mOperand.getAlphabet()) {
			result.addLetter(letter);
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
	 */
	private void refineBasedOnContexts(final Collection<RuleContext<LETTER, STATE>> contexts) {
		// Iterate all contexts and refine the partition
		for (final RuleContext<LETTER, STATE> context : contexts) {

			// Iterate each position
			for (int i = 0; i < context.getSourceSize(); i++) {
				final Set<STATE> sourceStatesAtPosition = context.getSourceStatesAtPosition(i);
				final STATE representative = context.getSourceRepresentativeAtPosition(i);
				final Set<STATE> block = this.mPartition.getContainingSet(representative);

				// Build the set representing states of that block which are not source states
				// at this position, i.e. the difference between the whole block and the source
				// states
				final Set<STATE> statesNotAtPosition = new HashSet<>(block.size() - sourceStatesAtPosition.size());
				for (final STATE stateOfBlock : block) {
					if (!sourceStatesAtPosition.contains(stateOfBlock)) {
						statesNotAtPosition.add(stateOfBlock);
					}
				}

				// Remove all pairs of the current relation that can not hold under the current
				// view. For example if there are states 1 and 2 at the current position in the
				// context, but the block consists of (1, 2, 3), then 3 should not stay in the
				// same block than 1 and 2 since the symmetric relation pairs (1, 3) and (2, 3)
				// can not hold.
				for (final STATE sourceStateAtPosition : sourceStatesAtPosition) {
					for (final STATE stateNotAtPosition : statesNotAtPosition) {
						this.mRelation.removePair(sourceStateAtPosition, stateNotAtPosition);
					}
				}
			}
		}

		// Update the partition such that it corresponds to the refined relation again.
		// TODO This step is extremely expensive. Find a way to update the partition at
		// iteration time.
		constructPartitionFromRelation(this.mRelation, this.mOperand.getStates());
		
		// TODO Update compound blocks
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
		// Select a progress Block
		final LinkedHashSet<STATE> progressBlock = this.mCompoundBlocks.iterator().next();

		if (initialRound) {
			// Find the representative of the block of final states as in the initial round
			// we always start with the set of final states
			for (final STATE representative : progressBlock) {
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
			return firstRepresentative;
		}
		return secondRepresentative;
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
