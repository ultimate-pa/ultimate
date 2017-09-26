package de.uni_freiburg.informatik.ultimate.automata.tree.operations.minimization;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;

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
	 * Factory used to merge states.
	 */
	private final IMergeStateFactory<STATE> mMergeFactory;
	/**
	 * The operand tree automaton to minimize.
	 */
	private final ITreeAutomatonBU<LETTER, STATE> mOperand;
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

		this.mResult = doOperation();
	}

	/**
	 * Executes this operation.
	 * 
	 * @return The resulting tree automaton obtained after minimizing the operand.
	 */
	private ITreeAutomatonBU<LETTER, STATE> doOperation() {
		// TODO Implement something meaningful
		throw new UnsupportedOperationException("Not implemented yet!");
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
	 * Gets the operand of this operation.
	 * 
	 * @return The operand of this operation
	 */
	protected ITreeAutomatonBU<LETTER, STATE> getOperand() {
		return this.mOperand;
	}

}
