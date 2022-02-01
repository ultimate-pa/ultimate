/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol;

/**
 * Basic configuration of SMTInterpol.
 *
 * @author Juergen Christ
 */
public interface Config {

	/// Competition mode
	public final static boolean COMPETITION = false;

	////// General configuration
	/// Create timing statistics
	public final static boolean PROFILE_TIME = !COMPETITION;
	/// Default log level
	public final static int DEFAULT_LOG_LEVEL = COMPETITION ? LogProxy.LOGLEVEL_ERROR : LogProxy.LOGLEVEL_INFO;
	/// Check the status set by the user against our check-sat status
	public final static boolean CHECK_STATUS_SET = !COMPETITION;

	////// Converter configuration
	/// Include redundant clauses for ite to achieve arc consistency
	public static final boolean REDUNDANT_ITE_CLAUSES = true;
	/// Number of occurrences when nested ors get transformed into literals.
	public static final int OCC_INLINE_THRESHOLD = 1;
	/// Number of occurrences when nested term ITEs are still inlined.
	public static final int OCC_INLINE_TERMITE_THRESHOLD = 1;

	////// DPLL configuration
	/// Activity limit
	public final static double LIMIT = 1e250;
	/// Unlearn clauses with activity below this threshold
	public final static double CLAUSE_UNLEARN_ACTIVITY = 1e-150;
	/// Activity factor for atoms
	public final static double ATOM_ACTIVITY_FACTOR = 1.1;
	/// Activity factor for clauses
	public final static double CLS_ACTIVITY_FACTOR = 1.01;
	/// Backtrack as far as possible
	public final static boolean DEEP_BACKTRACK = true;
	/// When to restart
	public final static int RESTART_FACTOR = 500;
	/// The default random seed
	// Currently delays random splits until the 10000th split...
	public final static long RANDOM_SEED = 11350294L;
	/// How often to split
	public final static int RANDOM_SPLIT_BASE = 10000;
	/// The frequency of random case splits
	/// (number per RANDOM_SPLIT_BASE elements)
	public final static int RANDOM_SPLIT_FREQ = 2;
	/// Compute an initial phase bias based on Jeruslaw Wang heuristics
	public static final boolean INITIAL_PHASE_BIAS_JW = true;
	/// Print information statistics on restarts
	public static final boolean PRINT_STATISTICS = !COMPETITION;

	////// Quantifier Support
	/// Debug unused variable elimination
	public final static boolean DEBUG_QVAR_ELIMINATION = true;
	/// Don't infer looping patterns
	public final static boolean FEATURE_BLOCK_LOOPING_PATTERN = true;

	////// Proofs
	/// Check proofs for propositional validity
	public final static boolean CHECK_PROP_PROOF = false;

	////// Printing of results
	/// Include line breaks in output of lists
	public final static boolean RESULTS_ONE_PER_LINE = true;
	/// Indentation for nested s-exprs
	public static final int INDENTATION = 2;

	////// Usage Checks
	/// Stronger checks for usage (e.g., closed check in assertTerm)
	public final static boolean STRONG_USAGE_CHECKS = !COMPETITION;

	////// Optimizer
	/// Call optimizer for every formula
	public final static boolean OPTIMIZE_ALWAYS = false;
	/// Call optimizer after lifting of Term ITEs
	public final static boolean OPTIMIZE_LIFTED = false;

	////// Linear arithmetic configuration
	/// When to switch back to Bland's Rule (#vars * this_factor)
	public static final int BLAND_USE_FACTOR = 5;

	/**
	 * Should we do paranoid and expensive asserts.
	 */
	public static final boolean EXPENSIVE_ASSERTS = false;

	////// Interpolator Configuration
	/// Should we check partial interpolants in interpolant-check-mode?
	public static final boolean DEEP_CHECK_INTERPOLANTS = false;

	////// Array solver configuration
	/// Should we always add a read on the base array of a store?
	/// If not, the read will only be created if the value sort is finite.
	public static final boolean ARRAY_ALWAYS_ADD_READ = false;

}
