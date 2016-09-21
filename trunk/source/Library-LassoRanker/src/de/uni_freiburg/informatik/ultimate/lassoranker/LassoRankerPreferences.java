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
import java.util.function.Consumer;

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
	 *
	 */
	public boolean mComputeIntegralHull;

	/**
	 * Enable the LassoPartitioneer that splits lassos into multiple independent components?
	 */
	public boolean mEnablePartitioneer;

	/**
	 * Add annotations to terms for debugging purposes
	 */
	public boolean mAnnotateTerms;

	/**
	 * If true, we use an external tool to solve the constraints. If false, we use SMTInterpol to solve the constraints.
	 */
	public boolean mExternalSolver;

	/**
	 * What shell command should be used to call the external smt solver?
	 */
	public String mExternalSolverCommand;

	/**
	 * Write SMT solver script to file.
	 */
	public boolean mDumpSmtSolverScript;

	/**
	 * Path to which the SMT solver script is written.
	 */
	public String mPathOfDumpedScript;

	/**
	 * Base name (without path) of the file to which the SMT solver script is written.
	 */
	public String mBaseNameOfDumpedScript;

	/**
	 * Overapproximate the result of RewriteArrays by dropping all conjuncts that are not-equals relations of indices.
	 * If the lasso does not contain arrays, this option has no effect. Otherwise setting this to true is unsound for
	 * nontermination analysis.
	 */
	public boolean mOverapproximateArrayIndexConnection;

	/**
	 * Defines what the {@link InequalityConverter} does while processing a (Sub-) Term that is nonlinear.
	 */
	public NlaHandling mNlaHandling;

	/**
	 * Use Matthias' (true) or Franks (false) map elimination implementation
	 */
	public boolean mUseOldMapElimination;

	/**
	 * Emulate push/pop using reset and re-asserting and re-declaring.
	 */
	private final boolean mFakeNonIncrementalScript;

	/**
	 * Default construction intializes default values
	 */
	public LassoRankerPreferences() {
		// all default values
		mFakeNonIncrementalScript = false;
		mUseOldMapElimination = false;
		mNlaHandling = NlaHandling.EXCEPTION;
		mOverapproximateArrayIndexConnection = false;
		mBaseNameOfDumpedScript = "LassoRankerScript";
		mPathOfDumpedScript = ".";
		mDumpSmtSolverScript = false;
		mComputeIntegralHull = false;
		mEnablePartitioneer = true;
		mAnnotateTerms = false;
		mExternalSolver = true;
		mExternalSolverCommand = "z3 -smt2 -in SMTLIB2_COMPLIANT=true ";
	}

	/**
	 * Copy constructor copies everything
	 */
	public LassoRankerPreferences(final LassoRankerPreferences other) {
		mComputeIntegralHull = other.mComputeIntegralHull;
		mEnablePartitioneer = other.mEnablePartitioneer;
		mAnnotateTerms = other.mAnnotateTerms;
		mExternalSolver = other.mExternalSolver;
		mExternalSolverCommand = other.mExternalSolverCommand;
		mDumpSmtSolverScript = other.mDumpSmtSolverScript;
		mPathOfDumpedScript = other.mPathOfDumpedScript;
		mBaseNameOfDumpedScript = other.mBaseNameOfDumpedScript;
		mOverapproximateArrayIndexConnection = other.mOverapproximateArrayIndexConnection;
		mNlaHandling = other.mNlaHandling;
		mUseOldMapElimination = other.mUseOldMapElimination;
		mFakeNonIncrementalScript = other.mFakeNonIncrementalScript;
	}

	/**
	 * Verify that the settings are self-consistent and sane. Only makes assertion calls.
	 */
	public void checkSanity() {
		assert mExternalSolverCommand != null;
		assert mPathOfDumpedScript != null;
		if (mDumpSmtSolverScript) {
			final File f = new File(mPathOfDumpedScript);
			assert f.exists();
			assert f.isDirectory();
			assert mBaseNameOfDumpedScript != null;
		}
	}

	/**
	 * Build a string description of the current preferences
	 */
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		feedSettingsString(a -> sb.append(a).append("\n"));
		return sb.toString();
	}

	public void feedSettingsString(final Consumer<String> consumer) {
		consumer.accept("Compute integeral hull: " + mComputeIntegralHull);
		consumer.accept("Enable LassoPartitioneer: " + mEnablePartitioneer);
		consumer.accept("Term annotations enabled: " + mAnnotateTerms);
		consumer.accept("Use exernal solver: " + mExternalSolver);
		consumer.accept("SMT solver command: " + mExternalSolverCommand);
		consumer.accept("Dump SMT script to file: " + mDumpSmtSolverScript);
		consumer.accept("Path of dumped script: " + mPathOfDumpedScript);
		consumer.accept("Filename of dumped script: " + mBaseNameOfDumpedScript);
		consumer.accept("MapElimAlgo: " + (mUseOldMapElimination ? "Matthias" : "Frank"));
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
		return new Settings(mFakeNonIncrementalScript, mExternalSolver, mExternalSolverCommand, timeoutSmtInterpol,
				null, mDumpSmtSolverScript, mPathOfDumpedScript, filenameDumpedScript);
	}
}
