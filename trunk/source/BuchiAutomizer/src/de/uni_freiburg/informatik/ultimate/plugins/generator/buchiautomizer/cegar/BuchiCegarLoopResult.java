/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 *
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerModuleDecompositionBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.TermcompProofBenchmark;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 * @param <L>
 */
public final class BuchiCegarLoopResult<L extends IIcfgTransition<?>> {
	/**
	 * Result of CEGAR loop iteration
	 * <ul>
	 * <li>SAFE: There is no feasible trace to an error location.
	 * <li>UNSAFE: There is a feasible trace to an error location (the underlying program has at least one execution
	 * which violates its specification).
	 * <li>UNKNOWN: We found a trace for which we could not decide feasibility or we found an infeasible trace but were
	 * not able to exclude it in abstraction refinement.
	 * <li>TIMEOUT: A timeout occurred.
	 * <li>INSUFFICIENT_THREADS: There are not enough threads to prove termination.
	 */
	public enum Result {
		TERMINATING, TIMEOUT, UNKNOWN, NONTERMINATING, INSUFFICIENT_THREADS
	}

	private final Result mResult;
	private final NestedWord<L> mStem;
	private final NestedWord<L> mLoop;
	private final Map<String, ILocation> mOverapproximations;
	private final ToolchainCanceledException mToolchainCancelledException;
	private final NonTerminationArgument mNonTerminationArgument;
	private final BuchiAutomizerModuleDecompositionBenchmark mMDBenchmark;
	private final TermcompProofBenchmark mTermcompProofBenchmark;

	private BuchiCegarLoopResult(final Result result, final NestedWord<L> stem, final NestedWord<L> loop,
			final Map<String, ILocation> overapproximations,
			final ToolchainCanceledException toolchainCancelledException,
			final NonTerminationArgument nonTerminationArgument,
			final BuchiAutomizerModuleDecompositionBenchmark mDBenchmark,
			final TermcompProofBenchmark termcompProofBenchmark) {
		mResult = result;
		mStem = stem;
		mLoop = loop;
		mOverapproximations = overapproximations;
		mToolchainCancelledException = toolchainCancelledException;
		mNonTerminationArgument = nonTerminationArgument;
		mMDBenchmark = mDBenchmark;
		mTermcompProofBenchmark = termcompProofBenchmark;
	}

	public static <L extends IIcfgTransition<?>> BuchiCegarLoopResult<L> constructTerminatingResult(
			final BuchiAutomizerModuleDecompositionBenchmark mDBenchmark,
			final TermcompProofBenchmark termcompProofBenchmark) {
		return new BuchiCegarLoopResult<>(Result.TERMINATING, null, null, null, null, null, mDBenchmark,
				termcompProofBenchmark);
	}

	public static <L extends IIcfgTransition<?>> BuchiCegarLoopResult<L> constructNonTerminatingResult(
			final NestedWord<L> stem, final NestedWord<L> loop, final NonTerminationArgument nonTerminationArgument,
			final BuchiAutomizerModuleDecompositionBenchmark mDBenchmark,
			final TermcompProofBenchmark termcompProofBenchmark) {
		return new BuchiCegarLoopResult<>(Result.NONTERMINATING, stem, loop, null, null, nonTerminationArgument,
				mDBenchmark, termcompProofBenchmark);
	}

	public static <L extends IIcfgTransition<?>> BuchiCegarLoopResult<L> constructUnknownResult(
			final NestedWord<L> stem, final NestedWord<L> loop, final Map<String, ILocation> overapproximations,
			final BuchiAutomizerModuleDecompositionBenchmark mDBenchmark,
			final TermcompProofBenchmark termcompProofBenchmark) {
		return new BuchiCegarLoopResult<>(Result.UNKNOWN, stem, loop, overapproximations, null, null, mDBenchmark,
				termcompProofBenchmark);
	}

	public static <L extends IIcfgTransition<?>> BuchiCegarLoopResult<L> constructTimeoutResult(
			final ToolchainCanceledException toolchainCancelledException,
			final BuchiAutomizerModuleDecompositionBenchmark mDBenchmark,
			final TermcompProofBenchmark termcompProofBenchmark) {
		return new BuchiCegarLoopResult<>(Result.TIMEOUT, null, null, null, toolchainCancelledException, null,
				mDBenchmark, termcompProofBenchmark);
	}

	public static <L extends IIcfgTransition<?>> BuchiCegarLoopResult<L> constructInsufficientThreadsResult() {
		return new BuchiCegarLoopResult<>(Result.INSUFFICIENT_THREADS, null, null, null, null, null, null, null);
	}

	public Result getResult() {
		return mResult;
	}

	public NestedWord<L> getStem() {
		if (mResult != Result.NONTERMINATING && mResult != Result.UNKNOWN) {
			throw new UnsupportedOperationException("Result " + mResult + " does not provide a counterexample.");
		}
		return mStem;
	}

	public NestedWord<L> getLoop() {
		if (mResult != Result.NONTERMINATING && mResult != Result.UNKNOWN) {
			throw new UnsupportedOperationException("Result " + mResult + " does not provide a counterexample.");
		}
		return mLoop;
	}

	public Map<String, ILocation> getOverapproximations() {
		if (mResult != Result.NONTERMINATING && mResult != Result.UNKNOWN) {
			throw new UnsupportedOperationException("Result " + mResult + " does not provide overapproximations.");
		}
		return mOverapproximations;
	}

	public ToolchainCanceledException getToolchainCancelledException() {
		if (mResult != Result.TIMEOUT) {
			throw new UnsupportedOperationException("Result " + mResult + " does not provide a TCE.");
		}
		return mToolchainCancelledException;
	}

	public NonTerminationArgument getNonTerminationArgument() {
		if (mResult != Result.NONTERMINATING) {
			throw new UnsupportedOperationException(
					"Result " + mResult + " does not provide a non-termination argument.");
		}
		return mNonTerminationArgument;
	}

	public BuchiAutomizerModuleDecompositionBenchmark getMDBenchmark() {
		return mMDBenchmark;
	}

	public TermcompProofBenchmark getTermcompProofBenchmark() {
		return mTermcompProofBenchmark;
	}
}
