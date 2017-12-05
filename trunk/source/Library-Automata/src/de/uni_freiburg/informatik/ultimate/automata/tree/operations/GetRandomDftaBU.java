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
package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.tree.StringRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ToolchainStorage;

/**
 * Creates a random deterministic finite bottom-up tree automaton (DFTA-BU)
 * using the helper class {@link AGetRandomFtaBU}. Note that the generation is
 * not uniform.
 * <p>
 * The algorithm is similar to the one described in<br>
 * <ul>
 * <li><i>2013 Hanneforth, Thomas et al. - Random Generation of Nondeterministic
 * Finite-State Tree Automata.</i></li>
 * </ul>
 * Roughly said the algorithm randomly selects source and destination nodes in
 * each round, connecting them with a random transition.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public final class GetRandomDftaBU extends AGetRandomFtaBU {
	/**
	 * The default seed to use for generation. It is not intended to change thus the
	 * result of using the default seed will always remain the same even in
	 * different JVM cycles.
	 */
	private static final long DEFAULT_SEED = 0;

	/**
	 * Demo usage of the random generator. Also used for debugging purpose.
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

		// Arguments for generation
		final int numberOfStates = 10;
		final int[] rankToNumberOfLetters = { 2, 1, 3 };
		final int[] rankToNumberOfTransitionsPerLetter = { 2, 5, 15 };
		final double acceptanceDensity = 0.2;

		final GetRandomDftaBU getRandomTree = new GetRandomDftaBU(services, numberOfStates, rankToNumberOfLetters,
				rankToNumberOfTransitionsPerLetter, acceptanceDensity);
		final TreeAutomatonBU<StringRankedLetter, String> tree = getRandomTree.getResult();

		// Output the generated tree
		System.out.println(tree);
	}

	/**
	 * Converts a given data structure listing transition densities into one holding
	 * absolute values. The method is checked and does not allow overflows, see the
	 * documentation section of the exceptions.
	 * 
	 * @param numberOfStates
	 *            The number of states the automaton has
	 * @param rankToTransitionDensity
	 *            The data structure to convert. Each index stands for the rank of a
	 *            letter. The value stored at an index represents the density
	 *            {@code (0 <= x <= 1)} of transitions of that rank. The method
	 *            needs to compute the upper bound of maximal possible transitions
	 *            which is {@code states^rank}. The computation is done exact thus
	 *            if numbers are big the method will take long.
	 * @return The converted data structure where each value lists the absolute
	 *         number of transitions per letter instead of their densities.
	 * @throws ArithmeticException
	 *             If the computation of {@code states^rank} does not fit into the
	 *             size of an {@link Integer}.
	 */
	private static final int[] convertTransitionDensitiesToNumbers(final int numberOfStates,
			final double[] rankToTransitionDensity) {
		final int[] rankToNumberOfTransitionsPerLetter = new int[rankToTransitionDensity.length];
		for (int rank = 0; rank < rankToTransitionDensity.length; rank++) {
			// In the deterministic case transitions with the same letter and also the exact
			// same source tuple are not allowed. That yields states^rank many source state
			// combinations for each letter.
			final BigInteger totalNumberOfTransitionsPerLetterExact = BigInteger.valueOf(numberOfStates).pow(rank);
			// This method checks for overflow and throws an exception if so
			final int totalNumberOfTransitionsPerLetter = totalNumberOfTransitionsPerLetterExact.intValueExact();

			final double transitionDensity = rankToTransitionDensity[rank];
			final int numberOfTransitionsPerLetter = densityToAbsolute(transitionDensity,
					totalNumberOfTransitionsPerLetter);

			rankToNumberOfTransitionsPerLetter[rank] = numberOfTransitionsPerLetter;
		}

		return rankToNumberOfTransitionsPerLetter;
	}

	/**
	 * If set then a method using transition densities instead of absolute amounts
	 * was chosen. Each index stands for the rank of a letter. The value stored at
	 * an index represents the density {@code (0 <= x <= 1)} of transitions of that
	 * rank. The density of nullary letters specify the amount of initial states.
	 */
	private double[] mRankToTransitionDensity = null;

	/**
	 * Constructor of a deterministic finite tree automaton for the
	 * {@code TestFileInterpreter}. This method uses a default seed that is not
	 * intended to change thus the result of this method, for same arguments, will
	 * always remain the same even in different JVM cycles. Use
	 * {@link #GetRandomDftaBU(AutomataLibraryServices, int, int[], double[], double, long)}
	 * if a seed should be specified.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param numberOfStates
	 *            The number of states {@code (>= 0)}
	 * @param rankToNumberOfLetters
	 *            Each index stands for the rank of a letter. The value stored at an
	 *            index represents the amount of letters with that rank should be
	 *            generated. Each value must be {@code >= 0}. Note that in order to
	 *            have initial states there must exist at least one nullary letter,
	 *            so <code>rankToNumberOfLetters[0]</code> should be set to a value
	 *            greater than <tt>zero</tt> if initial states are desired.
	 * @param rankToTransitionDensity
	 *            Each index stands for the rank of a letter. The value stored at an
	 *            index represents the density {@code (0 <= x <= 1)} of transitions
	 *            of that rank. Note that the density of nullary letters specify the
	 *            amount of initial states thus if initial states are desired
	 *            <code>rankToTransitionDensity[0]</code> should be set to a value
	 *            greater than <tt>zero</tt>. Also note that if there are many
	 *            states and ranks than a high density leads to an enormous amount
	 *            of transitions. With a full density {@code states^rank}
	 *            transitions will be created for each letter. In this case the
	 *            other constructor
	 *            {@link #GetRandomDftaBU(AutomataLibraryServices, int, int[], int[], double)}
	 *            may be more comfortable to use and also faster since this variant
	 *            needs to compute that bounds.
	 * @param acceptanceDensity
	 *            The acceptance density {@code (0 <= x <= 1)}. If <tt>1</tt> then
	 *            all states are accepting, if <tt>0</tt> then no state is
	 *            accepting.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public GetRandomDftaBU(final AutomataLibraryServices services, final int numberOfStates,
			final int[] rankToNumberOfLetters, final double[] rankToTransitionDensity, final double acceptanceDensity)
			throws AutomataOperationCanceledException {
		this(services, numberOfStates, rankToNumberOfLetters, rankToTransitionDensity, acceptanceDensity, DEFAULT_SEED);
	}

	/**
	 * Constructor of a deterministic finite tree automaton for the
	 * {@code TestFileInterpreter}.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param numberOfStates
	 *            The number of states {@code (>= 0)}
	 * @param rankToNumberOfLetters
	 *            Each index stands for the rank of a letter. The value stored at an
	 *            index represents the amount of letters with that rank should be
	 *            generated. Each value must be {@code >= 0}. Note that in order to
	 *            have initial states there must exist at least one nullary letter,
	 *            so <code>rankToNumberOfLetters[0]</code> should be set to a value
	 *            greater than <tt>zero</tt> if initial states are desired.
	 * @param rankToTransitionDensity
	 *            Each index stands for the rank of a letter. The value stored at an
	 *            index represents the density {@code (0 <= x <= 1)} of transitions
	 *            of that rank. Note that the density of nullary letters specify the
	 *            amount of initial states thus if initial states are desired
	 *            <code>rankToTransitionDensity[0]</code> should be set to a value
	 *            greater than <tt>zero</tt>. Also note that if there are many
	 *            states and ranks than a high density leads to an enormous amount
	 *            of transitions. With a full density {@code states^rank}
	 *            transitions will be created for each letter. In this case the
	 *            other constructor
	 *            {@link #GetRandomDftaBU(AutomataLibraryServices, int, int[], int[], double, long)}
	 *            may be more comfortable to use and also faster since this variant
	 *            needs to compute that bounds.
	 * @param acceptanceDensity
	 *            The acceptance density {@code (0 <= x <= 1)}. If <tt>1</tt> then
	 *            all states are accepting, if <tt>0</tt> then no state is
	 *            accepting.
	 * @param seed
	 *            The seed to use for random automaton generation.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public GetRandomDftaBU(final AutomataLibraryServices services, final int numberOfStates,
			final int[] rankToNumberOfLetters, final double[] rankToTransitionDensity, final double acceptanceDensity,
			final long seed) throws AutomataOperationCanceledException {
		super(services, numberOfStates, rankToNumberOfLetters,
				convertTransitionDensitiesToNumbers(numberOfStates, rankToTransitionDensity), acceptanceDensity, true,
				seed);
		this.mRankToTransitionDensity = rankToTransitionDensity;
		startGeneration();
	}

	/**
	 * Constructor of a deterministic finite tree automaton for the
	 * {@code TestFileInterpreter}. This method uses a default seed that is not
	 * intended to change thus the result of this method, for same arguments, will
	 * always remain the same even in different JVM cycles. Use
	 * {@link #GetRandomDftaBU(AutomataLibraryServices, int, int[], int[], double, long)}
	 * if a seed should be specified.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param numberOfStates
	 *            The number of states {@code (>= 0)}
	 * @param rankToNumberOfLetters
	 *            Each index stands for the rank of a letter. The value stored at an
	 *            index represents the amount of letters with that rank should be
	 *            generated. Each value must be {@code >= 0}. Note that in order to
	 *            have initial states there must exist at least one nullary letter,
	 *            so <code>rankToNumberOfLetters[0]</code> should be set to a value
	 *            greater than <tt>zero</tt> if initial states are desired.
	 * @param rankToNumberOfTransitionsPerLetter
	 *            Each index stands for the rank of a letter. The value stored at an
	 *            index represents the amount of transitions per letter of that rank
	 *            {@code (>= 0)}. The number of transitions of nullary letters
	 *            specify the amount of initial states thus if initial states are
	 *            desired <code>rankToNumberOfTransitionsPerLetter[0]</code> should
	 *            be set to a value greater than <tt>zero</tt>. Also note that the
	 *            number must be below the maximal possible amount of transitions
	 *            which is given by {@code states^rank}. For efficiency reasons this
	 *            object will not check validity for those upper bounds. If setting
	 *            higher values it is possible that this object never terminates the
	 *            generation process.
	 * @param acceptanceDensity
	 *            The acceptance density {@code (0 <= x <= 1)}. If <tt>1</tt> then
	 *            all states are accepting, if <tt>0</tt> then no state is
	 *            accepting.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public GetRandomDftaBU(final AutomataLibraryServices services, final int numberOfStates,
			final int[] rankToNumberOfLetters, final int[] rankToNumberOfTransitionsPerLetter,
			final double acceptanceDensity) throws AutomataOperationCanceledException {
		this(services, numberOfStates, rankToNumberOfLetters, rankToNumberOfTransitionsPerLetter, acceptanceDensity,
				DEFAULT_SEED);
	}

	/**
	 * Constructor of a deterministic finite tree automaton for the
	 * {@code TestFileInterpreter}.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param numberOfStates
	 *            The number of states {@code (>= 0)}
	 * @param rankToNumberOfLetters
	 *            Each index stands for the rank of a letter. The value stored at an
	 *            index represents the amount of letters with that rank should be
	 *            generated. Each value must be {@code >= 0}. Note that in order to
	 *            have initial states there must exist at least one nullary letter,
	 *            so <code>rankToNumberOfLetters[0]</code> should be set to a value
	 *            greater than <tt>zero</tt> if initial states are desired.
	 * @param rankToNumberOfTransitionsPerLetter
	 *            Each index stands for the rank of a letter. The value stored at an
	 *            index represents the amount of transitions per letter of that rank
	 *            {@code (>= 0)}. The number of transitions of nullary letters
	 *            specify the amount of initial states thus if initial states are
	 *            desired <code>rankToNumberOfTransitionsPerLetter[0]</code> should
	 *            be set to a value greater than <tt>zero</tt>. Also note that the
	 *            number must be below the maximal possible amount of transitions
	 *            which is given by {@code states^rank}. For efficiency reasons this
	 *            object will not check validity for those upper bounds. If setting
	 *            higher values it is possible that this object never terminates the
	 *            generation process.
	 * @param acceptanceDensity
	 *            The acceptance density {@code (0 <= x <= 1)}. If <tt>1</tt> then
	 *            all states are accepting, if <tt>0</tt> then no state is
	 *            accepting.
	 * @param seed
	 *            The seed to use for random automaton generation.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public GetRandomDftaBU(final AutomataLibraryServices services, final int numberOfStates,
			final int[] rankToNumberOfLetters, final int[] rankToNumberOfTransitionsPerLetter,
			final double acceptanceDensity, final long seed) throws AutomataOperationCanceledException {
		super(services, numberOfStates, rankToNumberOfLetters, rankToNumberOfTransitionsPerLetter, acceptanceDensity,
				true, seed);
		startGeneration();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.tree.operations.AGetRandomFtaBU#
	 * checkInputValidity()
	 */
	@Override
	protected void checkInputValidity() throws IllegalArgumentException {
		super.checkInputValidity();

		if (this.mRankToNumberOfTransitionsPerLetter.length > 0 && mRankToNumberOfTransitionsPerLetter[0] != 1) {
			throw new IllegalArgumentException(
					"The transitions of 0 ranked letters can be only 1 if the automaton is deterministic.");
		}
		// No extra checks if density variant was not chosen.
		if (this.mRankToTransitionDensity == null) {
			return;
		} 
		// Transition densities
		for (int i = 0; i < this.mRankToTransitionDensity.length; i++) {
			final double transitionDensity = this.mRankToTransitionDensity[i];
			// Check bounds
			if (transitionDensity < 0.0 || transitionDensity > 1.0) {
				throw new IllegalArgumentException("Illegal transition density.");
			}
		}
	}
}
