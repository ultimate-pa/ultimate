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
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;

public class TAPreferences {

	private final boolean m_Interprocedural;
	private final int m_MaxIterations;
	private final int m_watchIteration;
	private final Artifact m_Artifact;
	private final INTERPOLATION m_Interpolation;
	private final InterpolantAutomaton m_InterpolantAutomaton;
	private final boolean m_DumpAutomata;
	private final Format m_AutomataFormat;
	private final String m_DumpPath;
	private final InterpolantAutomatonEnhancement m_Determiniation;
	private final Minimization m_Minimize;
	private final boolean m_Hoare;
	private final Concurrency m_Concurrency;
	private final boolean m_SeperateViolationCheck = true;
	private final HoareTripleChecks m_HoareTripleChecks;
	private RcpPreferenceProvider m_Prefs;
	private final HoareAnnotationPositions m_HoareAnnotationPositions;

	public enum Artifact {
		ABSTRACTION, INTERPOLANT_AUTOMATON, NEG_INTERPOLANT_AUTOMATON, RCFG
	}


	public enum InterpolantAutomatonEnhancement {
		NONE, BESTAPPROXIMATION_DEPRECATED, SELFLOOP, EAGER, EAGER_CONSERVATIVE, 
		NO_SECOND_CHANCE, 
		PREDICATE_ABSTRACTION, PREDICATE_ABSTRACTION_CONSERVATIVE, 
		PREDICATE_ABSTRACTION_CANNIBALIZE,
	}


	public enum Concurrency {
		FINITE_AUTOMATA, PETRI_NET
	}

	public TAPreferences() {

		m_Prefs = new RcpPreferenceProvider(Activator.PLUGIN_ID);

		m_Interprocedural = m_Prefs
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_INTERPROCEDUTAL);

		m_MaxIterations = m_Prefs
				.getInt(TraceAbstractionPreferenceInitializer.LABEL_ITERATIONS);
		m_watchIteration = m_Prefs
				.getInt(TraceAbstractionPreferenceInitializer.LABEL_WATCHITERATION);

		m_Artifact = m_Prefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ARTIFACT,
				Artifact.class);

		m_Hoare = m_Prefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_HOARE,
				TraceAbstractionPreferenceInitializer.DEF_HOARE);
		
		m_HoareAnnotationPositions = m_Prefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_HOARE_Positions,
				TraceAbstractionPreferenceInitializer.DEF_HOARE_POSITIONS, HoareAnnotationPositions.class);

		m_Interpolation = m_Prefs.getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_INTERPOLATED_LOCS,
				INTERPOLATION.class);

		m_InterpolantAutomaton = m_Prefs.getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANT_AUTOMATON,
				InterpolantAutomaton.class);

		m_DumpAutomata = m_Prefs
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_DUMPAUTOMATA);
		
		m_AutomataFormat = m_Prefs.getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_AUTOMATAFORMAT,
				Format.class);

		m_DumpPath = m_Prefs.getString(TraceAbstractionPreferenceInitializer.LABEL_DUMPPATH);

		m_Determiniation = m_Prefs.getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_InterpolantAutomatonEnhancement,
				InterpolantAutomatonEnhancement.class);
		
		m_HoareTripleChecks = m_Prefs.getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_HoareTripleChecks, HoareTripleChecks.class);

		m_Minimize = m_Prefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_MINIMIZE,Minimization.class);

		m_Concurrency = m_Prefs.getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_CONCURRENCY, Concurrency.class);

		if (artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {
			throw new IllegalArgumentException("Show negated interpolant"
					+ "automaton not possible when using difference.");
		}

		if (m_watchIteration == 0
				&& (artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON || artifact() == Artifact.INTERPOLANT_AUTOMATON)) {
			throw new IllegalArgumentException("There is no interpolant"
					+ "automaton in iteration 0.");
		}

	}

	/**
	 * @return the interprocedural
	 */
	public boolean interprocedural() {
		return m_Interprocedural;
	}

	public boolean allErrorLocsAtOnce() {
		return m_Prefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_ALL_ERRORS_AT_ONCE);
	}
	
	public SolverMode solverMode() {
		return m_Prefs.getEnum(RcfgPreferenceInitializer.LABEL_Solver, SolverMode.class);
	}

	public String commandExternalSolver() {
		return m_Prefs.getString(RcfgPreferenceInitializer.LABEL_ExtSolverCommand);
	}
	
	public String logicForExternalSolver() {
		String logicForExternalSolver = m_Prefs
				.getString(RcfgPreferenceInitializer.LABEL_ExtSolverLogic);
		return logicForExternalSolver;
	}
	
	public boolean dumpSmtScriptToFile() {
		final boolean dumpSmtScriptToFile = m_Prefs
				.getBoolean(RcfgPreferenceInitializer.LABEL_DumpToFile);
		return dumpSmtScriptToFile;
	}

	public String pathOfDumpedScript() {
		final String pathOfDumpedScript  = m_Prefs
				.getString(RcfgPreferenceInitializer.LABEL_Path);
		return pathOfDumpedScript;
	}

	
//	final boolean dumpUsatCoreTrackBenchmark = (new UltimatePreferenceStore(RCFGBuilder.s_PLUGIN_ID))
//			.getBoolean(RcfgPreferenceInitializer.LABEL_DumpUnsatCoreTrackBenchmark);
//	
//	final boolean dumpMainTrackBenchmark = (new UltimatePreferenceStore(RCFGBuilder.s_PLUGIN_ID))
//			.getBoolean(RcfgPreferenceInitializer.LABEL_DumpMainTrackBenchmark);
	

	/**
	 * @return the maxIterations
	 */
	public int maxIterations() {
		return m_MaxIterations;
	}

	/**
	 * @return the prefObservedIteration
	 */
	public int watchIteration() {
		return m_watchIteration;
	}

	/**
	 * @return the artifact
	 */
	public Artifact artifact() {
		return m_Artifact;
	}

	public boolean useSeparateSolverForTracechecks() {
		return m_Prefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_SEPARATE_SOLVER);
	}
	
	
	
	/**
	 * @return the interpolatedLocs
	 */
	public INTERPOLATION interpolation() {
		return m_Interpolation;
	}

	/**
	 * @return the additionalEdges
	 */
	public InterpolantAutomaton interpolantAutomaton() {
		return m_InterpolantAutomaton;
	}

	/**
	 * @return the dumpAutomata
	 */
	public boolean dumpAutomata() {
		return m_DumpAutomata;
	}
	
	public Format getAutomataFormat() {
		return m_AutomataFormat;
	}

	/**
	 * @return the dumpPath
	 */
	public String dumpPath() {
		return m_DumpPath;
	}

	/**
	 * @return the determinization
	 */
	public InterpolantAutomatonEnhancement interpolantAutomatonEnhancement() {
		return m_Determiniation;
	}
	


	public HoareTripleChecks getHoareTripleChecks() {
		return m_HoareTripleChecks;
	}

	/**
	 * @return the difference
	 */
	public boolean differenceSenwa() {
		return m_Prefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_DIFFERENCE_SENWA);
	}

	/**
	 * @return the minimize
	 */
	public Minimization minimize() {
		return m_Minimize;
	}

	public Concurrency getConcurrency() {
		return m_Concurrency;
	}

	public boolean computeHoareAnnotation() {
		return m_Hoare;
	}
	
	public HoareAnnotationPositions getHoareAnnotationPositions() {
		return m_HoareAnnotationPositions;
	}

	public boolean seperateViolationCheck() {
		return m_SeperateViolationCheck;
	}

	public boolean cutOffRequiresSameTransition() {
		return m_Prefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_CUTOFF);
	}

	public boolean unfoldingToNet() {
		return m_Prefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_UNFOLDING2NET);
	}

	public String order() {
		return m_Prefs.getString(TraceAbstractionPreferenceInitializer.LABEL_ORDER);
	}


}
