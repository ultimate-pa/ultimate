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

/**
 * Global preferences for the LassoRanker. This type can be used together with {@link DefaultLassoRankerPreferences} to
 * create a valid {@link ILassoRankerPreferences} instance for use in {@link LassoAnalysis}.
 *
 * @see ILassoRankerPreferences
 * @see DefaultLassoRankerPreferences
 * @author Jan Leike
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class LassoRankerPreferences implements Serializable, ILassoRankerPreferences {
	private static final long serialVersionUID = 3253589986886574198L;

	private final boolean mComputeIntegralHull;

	private final boolean mEnablePartitioneer;

	private final boolean mAnnotateTerms;

	private final boolean mExternalSolver;

	private final String mExternalSolverCommand;

	private final boolean mDumpSmtSolverScript;

	private final String mPathOfDumpedScript;

	private final String mBaseNameOfDumpedScript;

	private final boolean mOverapproximateArrayIndexConnection;

	private final NlaHandling mNlaHandling;

	private final boolean mUseOldMapElimination;

	private final boolean mMapElimAddInequalities;

	private final boolean mMapElimOnlyTrivialImplicationsIndexAssignment;

	private final boolean mMapElimOnlyTrivialImplicationsArrayWrite;

	private final boolean mMapElimOnlyIndicesInFormula;

	private final boolean mFakeNonIncrementalScript;

	/**
	 * Copy constructor. Call this with an anonymous extension of {@link DefaultLassoRankerPreferences} to create a
	 * custom {@link ILassoRankerPreferences} instance.
	 */
	public LassoRankerPreferences(final ILassoRankerPreferences prefs) {
		// all default values
		this(prefs.isComputeIntegralHull(), prefs.isEnablePartitioneer(), prefs.isAnnotateTerms(),
				prefs.isExternalSolver(), prefs.getExternalSolverCommand(), prefs.isDumpSmtSolverScript(),
				prefs.getPathOfDumpedScript(), prefs.getBaseNameOfDumpedScript(),
				prefs.isOverapproximateArrayIndexConnection(), prefs.getNlaHandling(), prefs.isUseOldMapElimination(),
				prefs.isMapElimAddInequalities(), prefs.isMapElimOnlyTrivialImplicationsIndexAssignment(),
				prefs.isMapElimOnlyTrivialImplicationsArrayWrite(), prefs.isMapElimOnlyIndicesInFormula(),
				prefs.isFakeNonIncrementalScript());
	}

	/**
	 * Construct a full instance.
	 */
	private LassoRankerPreferences(final boolean computeIntegralHull, final boolean enablePartitioneer,
			final boolean annotateTerms, final boolean externalSolver, final String externalSolverCommand,
			final boolean dumpSmtSolverScript, final String pathOfDumpedScript, final String baseNameOfDumpedScript,
			final boolean overapproximateArrayIndexConnection, final NlaHandling nlaHandling,
			final boolean useOldMapElimination, final boolean mapElimAddInequalities,
			final boolean mapElimOnlyTrivialImplicationsIndexAssignment,
			final boolean mapElimOnlyTrivialImplicationsArrayWrite, final boolean mapElimOnlyIndicesInFormula,
			final boolean fakeNonIncrementalScript) {
		mComputeIntegralHull = computeIntegralHull;
		mEnablePartitioneer = enablePartitioneer;
		mAnnotateTerms = annotateTerms;
		mExternalSolver = externalSolver;
		mExternalSolverCommand = externalSolverCommand;
		mDumpSmtSolverScript = dumpSmtSolverScript;
		mPathOfDumpedScript = pathOfDumpedScript;
		mBaseNameOfDumpedScript = baseNameOfDumpedScript;
		mOverapproximateArrayIndexConnection = overapproximateArrayIndexConnection;
		mNlaHandling = nlaHandling;
		mUseOldMapElimination = useOldMapElimination;
		mMapElimAddInequalities = mapElimAddInequalities;
		mMapElimOnlyTrivialImplicationsIndexAssignment = mapElimOnlyTrivialImplicationsIndexAssignment;
		mMapElimOnlyTrivialImplicationsArrayWrite = mapElimOnlyTrivialImplicationsArrayWrite;
		mMapElimOnlyIndicesInFormula = mapElimOnlyIndicesInFormula;
		mFakeNonIncrementalScript = fakeNonIncrementalScript;
		assert isSane() : "Settings are invalid";
	}

	/**
	 * Verify that the settings are self-consistent and sane. Only makes assertion calls.
	 */
	private boolean isSane() {
		if (mExternalSolverCommand != null && mPathOfDumpedScript != null) {
			if (mDumpSmtSolverScript) {
				final File f = new File(mPathOfDumpedScript);
				return f.exists() && f.isDirectory() && mBaseNameOfDumpedScript != null;
			}
			return true;
		}
		return false;
	}

	/**
	 * Should the polyhedra for stem and loop be made integral for integer programs? (Not yet implemented.)
	 *
	 */
	@Override
	public boolean isComputeIntegralHull() {
		return mComputeIntegralHull;
	}

	/**
	 * Enable the LassoPartitioneer that splits lassos into multiple independent components?
	 */
	@Override
	public boolean isEnablePartitioneer() {
		return mEnablePartitioneer;
	}

	/**
	 * Add annotations to terms for debugging purposes
	 */
	@Override
	public boolean isAnnotateTerms() {
		return mAnnotateTerms;
	}

	/**
	 * If true, we use an external tool to solve the constraints. If false, we use SMTInterpol to solve the constraints.
	 */
	@Override
	public boolean isExternalSolver() {
		return mExternalSolver;
	}

	/**
	 * What shell command should be used to call the external smt solver?
	 */
	@Override
	public String getExternalSolverCommand() {
		return mExternalSolverCommand;
	}

	/**
	 * Write SMT solver script to file.
	 */
	@Override
	public boolean isDumpSmtSolverScript() {
		return mDumpSmtSolverScript;
	}

	/**
	 * Path to which the SMT solver script is written.
	 */
	@Override
	public String getPathOfDumpedScript() {
		return mPathOfDumpedScript;
	}

	/**
	 * Base name (without path) of the file to which the SMT solver script is written.
	 */
	@Override
	public String getBaseNameOfDumpedScript() {
		return mBaseNameOfDumpedScript;
	}

	/**
	 * Overapproximate the result of RewriteArrays by dropping all conjuncts that are not-equals relations of indices.
	 * If the lasso does not contain arrays, this option has no effect. Otherwise setting this to true is unsound for
	 * nontermination analysis.
	 */
	@Override
	public boolean isOverapproximateArrayIndexConnection() {
		return mOverapproximateArrayIndexConnection;
	}

	/**
	 * Defines what the {@link InequalityConverter} does while processing a (Sub-) Term that is nonlinear.
	 */
	@Override
	public NlaHandling getNlaHandling() {
		return mNlaHandling;
	}

	/**
	 * Use Matthias' (true) or Franks (false) map elimination implementation
	 */
	@Override
	public boolean isUseOldMapElimination() {
		return mUseOldMapElimination;
	}

	@Override
	public boolean isMapElimAddInequalities() {
		return mMapElimAddInequalities;
	}

	@Override
	public boolean isMapElimOnlyTrivialImplicationsIndexAssignment() {
		return mMapElimOnlyTrivialImplicationsIndexAssignment;
	}

	@Override
	public boolean isMapElimOnlyTrivialImplicationsArrayWrite() {
		return mMapElimOnlyTrivialImplicationsArrayWrite;
	}

	@Override
	public boolean isMapElimOnlyIndicesInFormula() {
		return mMapElimOnlyIndicesInFormula;
	}

	/**
	 * Emulate push/pop using reset and re-asserting and re-declaring.
	 */
	@Override
	public boolean isFakeNonIncrementalScript() {
		return mFakeNonIncrementalScript;
	}
}
