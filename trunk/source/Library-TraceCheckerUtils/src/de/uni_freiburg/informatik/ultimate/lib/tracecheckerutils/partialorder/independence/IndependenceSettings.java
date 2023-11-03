/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;

/**
 * Bundles various settings specifying an independence relation to be used.
 *
 * @see de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public final class IndependenceSettings {

	public static final IndependenceType DEFAULT_INDEPENDENCE_TYPE = IndependenceType.SEMANTIC;
	public static final AbstractionType DEFAULT_ABSTRACTION_TYPE = AbstractionType.NONE;
	public static final boolean DEFAULT_USE_CONDITIONAL = true;
	public static final boolean DEFAULT_USE_SEMICOMMUTATIVITY = true;
	public static final ExternalSolver DEFAULT_SOLVER = ExternalSolver.Z3;
	public static final long DEFAULT_SOLVER_TIMEOUT = 1000;

	/**
	 * Specifies the basic type of independence check.
	 */
	public enum IndependenceType {
		/**
		 * Use only syntactic criteria (e.g. accessed variables) to determine commutativity.
		 */
		SYNTACTIC,
		/**
		 * Use an SMT solver to determine commutativity based on action semantics.
		 */
		SEMANTIC,
	}

	/**
	 * Specifies a kind of abstraction to be integrated in the independence check.
	 */
	public enum AbstractionType {
		/**
		 * Do not apply any abstraction.
		 */
		NONE,
		/**
		 * Apply an abstraction that eliminates variables not used in the current proof candidate.
		 *
		 * @see de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.VariableAbstraction
		 */
		VARIABLES_GLOBAL,
		/**
		 * Apply an abstraction that eliminates variables not used in Hoare triples for the abstracted statement in the
		 * current proof candidate.
		 *
		 * @see de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.SpecificVariableAbstraction
		 */
		VARIABLES_LOCAL,
		/**
		 * Represents abstract independence that considers statements independent if one of them is a "looper" in the
		 * current proof candidate.
		 *
		 * @see de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.LooperIndependenceRelation
		 */
		LOOPER
	}

	private final IndependenceType mIndependenceType;
	private final AbstractionType mAbstractionType;
	private final boolean mUseConditional;
	private final boolean mUseSemiCommutativity;

	private final ExternalSolver mSolver;
	private final long mSolverTimeout;

	/**
	 * Creates default settings for a simple independence relation.
	 */
	public IndependenceSettings() {
		this(DEFAULT_INDEPENDENCE_TYPE, DEFAULT_ABSTRACTION_TYPE, DEFAULT_USE_CONDITIONAL,
				DEFAULT_USE_SEMICOMMUTATIVITY, DEFAULT_SOLVER, DEFAULT_SOLVER_TIMEOUT);
	}

	public IndependenceSettings(final IndependenceType independenceType, final AbstractionType abstractionType,
			final boolean useConditional, final boolean useSemiCommutativity, final ExternalSolver solver,
			final long solverTimeout) {
		mIndependenceType = independenceType;
		mAbstractionType = abstractionType;
		mUseConditional = useConditional;
		mUseSemiCommutativity = useSemiCommutativity;
		mSolver = solver;
		mSolverTimeout = solverTimeout;
	}

	public IndependenceType getIndependenceType() {
		return mIndependenceType;
	}

	public AbstractionType getAbstractionType() {
		return mAbstractionType;
	}

	public boolean useConditional() {
		return mUseConditional;
	}

	public boolean useSemiCommutativity() {
		return mUseSemiCommutativity;
	}

	public ExternalSolver getSolver() {
		return mSolver;
	}

	public long getSolverTimeout() {
		return mSolverTimeout;
	}

	@Override
	public String toString() {
		if (mIndependenceType == IndependenceType.SYNTACTIC) {
			return "[IndependenceType=" + mIndependenceType + ", AbstractionType=" + mAbstractionType
					+ ", UseConditional=<UNSUPPORTED>, UseSemiCommutativity=<UNSUPPORTED>, "
					+ "Solver=<NOT_USED>, SolverTimeout=<NOT_USED>]";
		}
		return "[IndependenceType=" + mIndependenceType + ", AbstractionType=" + mAbstractionType + ", UseConditional="
				+ mUseConditional + ", UseSemiCommutativity=" + mUseSemiCommutativity + ", Solver=" + mSolver
				+ ", SolverTimeout=" + mSolverTimeout + "ms]";
	}
}
