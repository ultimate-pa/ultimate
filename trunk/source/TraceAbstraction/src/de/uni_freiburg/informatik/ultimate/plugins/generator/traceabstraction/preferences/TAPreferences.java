package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
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
	private final String m_DumpPath;
	private final InterpolantAutomatonEnhancement m_Determiniation;
	private final Minimization m_Minimize;
	private final boolean m_Hoare;
	private final Concurrency m_Concurrency;
	private final boolean m_SeperateViolationCheck = true;
	private UltimatePreferenceStore m_Prefs;

	public enum Artifact {
		ABSTRACTION, INTERPOLANT_AUTOMATON, NEG_INTERPOLANT_AUTOMATON, RCFG
	}


	public enum InterpolantAutomatonEnhancement {
		NONE, BESTAPPROXIMATION_DEPRECATED, SELFLOOP, EAGER, PREDICATE_ABSTRACTION
	}


	public enum Concurrency {
		FINITE_AUTOMATA, PETRI_NET
	}

	public TAPreferences() {

		m_Prefs = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);

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

		m_Interpolation = m_Prefs.getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_INTERPOLATED_LOCS,
				INTERPOLATION.class);

		m_InterpolantAutomaton = m_Prefs.getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANT_AUTOMATON,
				InterpolantAutomaton.class);

		m_DumpAutomata = m_Prefs
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_DUMPAUTOMATA);

		m_DumpPath = m_Prefs.getString(TraceAbstractionPreferenceInitializer.LABEL_DUMPPATH);

		m_Determiniation = m_Prefs.getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_InterpolantAutomatonEnhancement,
				InterpolantAutomatonEnhancement.class);

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

	/**
	 * @return the dumpPath
	 */
	public String dumpPath() {
		return m_DumpPath;
	}

	/**
	 * @return the determinization
	 */
	public InterpolantAutomatonEnhancement determinization() {
		return m_Determiniation;
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
