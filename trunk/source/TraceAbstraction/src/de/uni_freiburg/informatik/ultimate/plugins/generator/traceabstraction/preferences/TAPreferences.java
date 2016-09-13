/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences;

import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;

public class TAPreferences {

	private final boolean mInterprocedural;
	private final int mMaxIterations;
	private final int mWatchIteration;
	private final Artifact mArtifact;
	private final InterpolationTechnique mInterpolation;
	private final InterpolantAutomaton mInterpolantAutomaton;
	private final boolean mDumpAutomata;
	private final Format mAutomataFormat;
	private final String mDumpPath;
	private final InterpolantAutomatonEnhancement mDeterminiation;
	private final Minimization mMinimize;
	private final boolean mHoare;
	private final Concurrency mConcurrency;
	private static final boolean SEPARATE_VIOLATION_CHECK = true;
	private final HoareTripleChecks mHoareTripleChecks;
	private final IPreferenceProvider mPrefs;
	private final HoareAnnotationPositions mHoareAnnotationPositions;

	public enum Artifact {
		ABSTRACTION, INTERPOLANT_AUTOMATON, NEG_INTERPOLANT_AUTOMATON, RCFG
	}

	public enum InterpolantAutomatonEnhancement {
		NONE, BESTAPPROXIMATION_DEPRECATED, SELFLOOP, EAGER, EAGER_CONSERVATIVE, NO_SECOND_CHANCE, PREDICATE_ABSTRACTION, PREDICATE_ABSTRACTION_CONSERVATIVE, PREDICATE_ABSTRACTION_CANNIBALIZE,
	}

	public enum Concurrency {
		FINITE_AUTOMATA, PETRI_NET
	}

	public TAPreferences(final IUltimateServiceProvider services) {

		mPrefs = services.getPreferenceProvider(Activator.PLUGIN_ID);

		mInterprocedural = mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_INTERPROCEDUTAL);

		mMaxIterations = mPrefs.getInt(TraceAbstractionPreferenceInitializer.LABEL_ITERATIONS);
		mWatchIteration = mPrefs.getInt(TraceAbstractionPreferenceInitializer.LABEL_WATCHITERATION);

		mArtifact = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ARTIFACT, Artifact.class);

		mHoare = mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_HOARE,
				TraceAbstractionPreferenceInitializer.DEF_HOARE);

		mHoareAnnotationPositions = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_HOARE_Positions,
				TraceAbstractionPreferenceInitializer.DEF_HOARE_POSITIONS, HoareAnnotationPositions.class);

		mInterpolation = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLATED_LOCS,
				InterpolationTechnique.class);

		mInterpolantAutomaton = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANT_AUTOMATON,
				InterpolantAutomaton.class);

		mDumpAutomata = mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_DUMPAUTOMATA);

		mAutomataFormat = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_AUTOMATAFORMAT, Format.class);

		mDumpPath = mPrefs.getString(TraceAbstractionPreferenceInitializer.LABEL_DUMPPATH);

		mDeterminiation = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANT_AUTOMATON_ENHANCEMENT,
				InterpolantAutomatonEnhancement.class);

		mHoareTripleChecks =
				mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_HoareTripleChecks, HoareTripleChecks.class);

		mMinimize = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_MINIMIZE, Minimization.class);

		mConcurrency = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_CONCURRENCY, Concurrency.class);

		if (artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {
			throw new IllegalArgumentException(
					"Show negated interpolant" + "automaton not possible when using difference.");
		}

		if (mWatchIteration == 0
				&& (artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON || artifact() == Artifact.INTERPOLANT_AUTOMATON)) {
			throw new IllegalArgumentException("There is no interpolant" + "automaton in iteration 0.");
		}

	}

	/**
	 * @return the interprocedural
	 */
	public boolean interprocedural() {
		return mInterprocedural;
	}

	public boolean allErrorLocsAtOnce() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_ALL_ERRORS_AT_ONCE);
	}

	public SolverMode solverMode() {
		return mPrefs.getEnum(RcfgPreferenceInitializer.LABEL_Solver, SolverMode.class);
	}

	public String commandExternalSolver() {
		return mPrefs.getString(RcfgPreferenceInitializer.LABEL_ExtSolverCommand);
	}

	public String logicForExternalSolver() {
		final String logicForExternalSolver = mPrefs.getString(RcfgPreferenceInitializer.LABEL_ExtSolverLogic);
		return logicForExternalSolver;
	}

	public boolean dumpSmtScriptToFile() {
		final boolean dumpSmtScriptToFile = mPrefs.getBoolean(RcfgPreferenceInitializer.LABEL_DumpToFile);
		return dumpSmtScriptToFile;
	}

	public String pathOfDumpedScript() {
		final String pathOfDumpedScript = mPrefs.getString(RcfgPreferenceInitializer.LABEL_Path);
		return pathOfDumpedScript;
	}

	/**
	 * @return the maxIterations
	 */
	public int maxIterations() {
		return mMaxIterations;
	}

	/**
	 * @return the prefObservedIteration
	 */
	public int watchIteration() {
		return mWatchIteration;
	}

	/**
	 * @return the artifact
	 */
	public Artifact artifact() {
		return mArtifact;
	}

	public boolean useSeparateSolverForTracechecks() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_SEPARATE_SOLVER);
	}

	/**
	 * @return the interpolatedLocs
	 */
	public InterpolationTechnique interpolation() {
		return mInterpolation;
	}

	/**
	 * @return the additionalEdges
	 */
	public InterpolantAutomaton interpolantAutomaton() {
		return mInterpolantAutomaton;
	}

	/**
	 * @return the dumpAutomata
	 */
	public boolean dumpAutomata() {
		return mDumpAutomata;
	}

	public Format getAutomataFormat() {
		return mAutomataFormat;
	}

	/**
	 * @return the dumpPath
	 */
	public String dumpPath() {
		return mDumpPath;
	}

	/**
	 * @return the determinization
	 */
	public InterpolantAutomatonEnhancement interpolantAutomatonEnhancement() {
		return mDeterminiation;
	}

	public HoareTripleChecks getHoareTripleChecks() {
		return mHoareTripleChecks;
	}

	/**
	 * @return the difference
	 */
	public boolean differenceSenwa() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_DIFFERENCE_SENWA);
	}

	/**
	 * @return the minimize
	 */
	public Minimization minimize() {
		return mMinimize;
	}

	public Concurrency getConcurrency() {
		return mConcurrency;
	}

	public boolean computeHoareAnnotation() {
		return mHoare;
	}

	public HoareAnnotationPositions getHoareAnnotationPositions() {
		return mHoareAnnotationPositions;
	}

	public boolean seperateViolationCheck() {
		return SEPARATE_VIOLATION_CHECK;
	}

	public boolean cutOffRequiresSameTransition() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_CUTOFF);
	}

	public boolean unfoldingToNet() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_UNFOLDING2NET);
	}

	public String order() {
		return mPrefs.getString(TraceAbstractionPreferenceInitializer.LABEL_ORDER);
	}

	public SimplicationTechnique getSimplificationTechnique() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_SIMPLIFICATION_TECHNIQUE,
				SimplicationTechnique.class);
	}

	public XnfConversionTechnique getXnfConversionTechnique() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_XNF_CONVERSION_TECHNIQUE,
				XnfConversionTechnique.class);
	}

	public boolean fakeNonIncrementalSolver() {
		return mPrefs.getBoolean(RcfgPreferenceInitializer.LABEL_FakeNonIncrementalScript);
	}
}
