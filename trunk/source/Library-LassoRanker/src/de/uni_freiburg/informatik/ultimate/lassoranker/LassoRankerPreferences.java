/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.io.File;
import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.lassoranker.variables.InequalityConverter;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.InequalityConverter.NlaHandling;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;

/**
 * Global preferences for LassoRanker. These values are constant for the lifetime of the LassoAnalysis object
 *
 * This class functions much like a struct and is implemented like one.
 *
 * @author Jan Leike
 */
public class LassoRankerPreferences implements Serializable {
	private static final long serialVersionUID = 3253589986886574198L;

	/**
	 * Should the polyhedra for stem and loop be made integral for integer programs? (Not yet implemented.)
	 */
	public boolean compute_integral_hull = false; // Default: false

	/**
	 * Enable the LassoPartitioneer that splits lassos into multiple independent components?
	 */
	public boolean enable_partitioneer = true; // Default: true

	/**
	 * Add annotations to terms for debugging purposes
	 */
	public boolean annotate_terms = false; // Default: false

	/**
	 * If true, we use an external tool to solve the constraints. If false, we use SMTInterpol to solve the constraints.
	 */
	public boolean externalSolver = true; // Default: true

	/**
	 * What shell command should be used to call the external smt solver?
	 */
	public String smt_solver_command = "z3 -smt2 -in SMTLIB2_COMPLIANT=true ";

	/**
	 * Write SMT solver script to file.
	 */
	public boolean dumpSmtSolverScript = false; // Default: false

	/**
	 * Path to which the SMT solver script is written.
	 */
	public String path_of_dumped_script = "."; // Default: "."

	/**
	 * Base name (without path) of the file to which the SMT solver script is written.
	 */
	public String baseNameOfDumpedScript = "LassoRankerScript";

	/**
	 * Overapproximate the result of RewriteArrays by dropping all conjuncts that are not-equals relations of indices.
	 * If the lasso does not contain arrays, this option has no effect. Otherwise setting this to true is unsound for
	 * nontermination analysis.
	 */
	public boolean overapproximateArrayIndexConnection = false;

	/**
	 * Defines what the {@link InequalityConverter} does while processing a (Sub-) Term that is nonlinear.
	 */
	public NlaHandling nlaHandling = NlaHandling.EXCEPTION;

	/**
	 * Use Matthias' (true) or Franks (false) map elimination implementation
	 */
	public boolean useOldMapElimination = false;

	/**
	 * Emulate push/pop using reset and re-asserting and re-declaring.
	 */
	private final boolean mFakeNonIncrementalScript = false;

	/**
	 * Default construction intializes default values
	 */
	public LassoRankerPreferences() {
	}

	/**
	 * Copy constructor copies everything
	 */
	public LassoRankerPreferences(final LassoRankerPreferences other) {
		compute_integral_hull = other.compute_integral_hull;
		enable_partitioneer = other.enable_partitioneer;
		annotate_terms = other.annotate_terms;
		externalSolver = other.externalSolver;
		smt_solver_command = other.smt_solver_command;
		dumpSmtSolverScript = other.dumpSmtSolverScript;
		path_of_dumped_script = other.path_of_dumped_script;
		baseNameOfDumpedScript = other.baseNameOfDumpedScript;
		overapproximateArrayIndexConnection = other.overapproximateArrayIndexConnection;
		nlaHandling = other.nlaHandling;
		useOldMapElimination = other.useOldMapElimination;
	}

	/**
	 * Verify that the settings are self-consistent and sane. Only makes assertion calls.
	 */
	public void checkSanity() {
		assert smt_solver_command != null;
		assert path_of_dumped_script != null;
		if (dumpSmtSolverScript) {
			final File f = new File(path_of_dumped_script);
			assert f.exists();
			assert f.isDirectory();
			assert baseNameOfDumpedScript != null;
		}
	}

	/**
	 * Build a string description of the current preferences
	 */
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Compute integeral hull: ");
		sb.append(compute_integral_hull);
		sb.append("\nEnable LassoPartitioneer: ");
		sb.append(enable_partitioneer);
		sb.append("\nTerm annotations enabled: ");
		sb.append(annotate_terms);
		sb.append("\nUse exernal solver: ");
		sb.append(externalSolver);
		sb.append("\nSMT solver command: ");
		sb.append(smt_solver_command);
		sb.append("\nDump SMT script to file: ");
		sb.append(dumpSmtSolverScript);
		sb.append("\nPath of dumped script: ");
		sb.append(path_of_dumped_script);
		sb.append("\nFilename of dumped script: ");
		sb.append(baseNameOfDumpedScript);
		sb.append("\nMapElimAlgo: ");
		sb.append(useOldMapElimination ? "Matthias" : "Frank");
		return sb.toString();
	}

	/**
	 * Construct Settings for building a solver.
	 *
	 * @param filenameDumpedScript
	 *            basename (without path and file ending) of the SMT script that is dumped if dumpSmtSolverScript is set
	 *            to true
	 * @return a Settings object that allows us to build a new solver.
	 */
	public Settings getSolverConstructionSettings(final String filenameDumpedScript) {
		final long timeoutSmtInterpol = 365 * 24 * 60 * 60 * 1000;
		return new Settings(mFakeNonIncrementalScript , externalSolver, smt_solver_command, timeoutSmtInterpol, null, dumpSmtSolverScript,
				path_of_dumped_script, filenameDumpedScript);
	}
}
