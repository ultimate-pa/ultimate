package de.uni_freiburg.informatik.ultimate.automata.tree.operations.minimization;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
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
	 * Factory used to merge states.
	 */
	private final IMergeStateFactory<STATE> mMergeFactory;
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
		this.mMergeFactory = mergeFactory;
		this.mOperand = operand;

		this.mResult = null;
		this.mRelation = new SymmetricHashRelation<>();

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
	 * Executes this operation.
	 * 
	 * @return The resulting tree automaton obtained after minimizing the operand.
	 */
	private ITreeAutomatonBU<LETTER, STATE> doOperation() {
		initPartition();

		// TODO Refine the partition until it represents valid a bisimulation

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

		// Setup the initial partition
		this.mPartition = new UnionFind<>();
		this.mPartition.addEquivalenceClass(finalBlock);
		this.mPartition.addEquivalenceClass(nonFinalBlock);

		// Create the corresponding relation
		for (final STATE representative : this.mPartition.getAllRepresentatives()) {
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
	 * Gets the operand of this operation.
	 * 
	 * @return The operand of this operation
	 */
	protected ITreeAutomatonBU<LETTER, STATE> getOperand() {
		return this.mOperand;
	}

}
