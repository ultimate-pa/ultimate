package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.PreferenceInitializer.INTERPOLATION;

public class TAPreferences {

	private final boolean m_Interprocedural;
	private final int m_MaxIterations;
	private final int m_watchIteration;
	private final Artifact m_Artifact;
	private final INTERPOLATION m_Interpolation;
	private final boolean m_Edges2True;
	private final InterpolantAutomaton m_InterpolantAutomaton;
	private final boolean m_DumpAutomata;
	private final String m_DumpPath;
	private final Determinization m_Determiniation;
	private final boolean m_Minimize;
	private final boolean m_Hoare;
	private final Concurrency m_Concurrency;
	private final boolean m_SeperateViolationCheck = true;
	private UltimatePreferenceStore m_Prefs;

	public enum Artifact {
		ABSTRACTION, INTERPOLANT_AUTOMATON, NEG_INTERPOLANT_AUTOMATON, RCFG
	}

	public enum InterpolantAutomaton {
		CANONICAL, TOTALINTERPOLATION, SINGLETRACE, TWOTRACK
	}

	public enum Determinization {
		POWERSET, BESTAPPROXIMATION, SELFLOOP, STRONGESTPOST, EAGERPOST, LAZYPOST
	}

	public enum Concurrency {
		FINITE_AUTOMATA, PETRI_NET
	}

	public TAPreferences() {

		m_Prefs = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);

		m_Interprocedural = m_Prefs
				.getBoolean(PreferenceInitializer.LABEL_INTERPROCEDUTAL);

		m_MaxIterations = m_Prefs
				.getInt(PreferenceInitializer.LABEL_ITERATIONS);
		m_watchIteration = m_Prefs
				.getInt(PreferenceInitializer.LABEL_WATCHITERATION);

		m_Artifact = m_Prefs.getEnum(PreferenceInitializer.LABEL_ARTIFACT,
				Artifact.class);

		m_Hoare = m_Prefs.getBoolean(PreferenceInitializer.LABEL_HOARE,
				PreferenceInitializer.DEF_HOARE);

		m_Interpolation = m_Prefs.getEnum(
				PreferenceInitializer.LABEL_INTERPOLATED_LOCS,
				INTERPOLATION.class);

		m_Edges2True = m_Prefs
				.getBoolean(PreferenceInitializer.LABEL_EDGES2TRUE);

		m_InterpolantAutomaton = m_Prefs.getEnum(
				PreferenceInitializer.LABEL_InterpolantAutomaton,
				InterpolantAutomaton.class);

		m_DumpAutomata = m_Prefs
				.getBoolean(PreferenceInitializer.LABEL_DUMPAUTOMATA);

		m_DumpPath = m_Prefs.getString(PreferenceInitializer.LABEL_DUMPPATH);

		m_Determiniation = m_Prefs.getEnum(
				PreferenceInitializer.LABEL_DETERMINIZATION,
				Determinization.class);

		m_Minimize = m_Prefs.getBoolean(PreferenceInitializer.LABEL_MINIMIZE);

		m_Concurrency = m_Prefs.getEnum(
				PreferenceInitializer.LABEL_CONCURRENCY, Concurrency.class);

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
		return m_Prefs.getBoolean(PreferenceInitializer.LABEL_AllErrorsAtOnce);
	}


	/**
	 * @return the timeout in seconds
	 */
	public int timeout() {
		return m_Prefs.getInt(PreferenceInitializer.LABEL_TIMEOUT);
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
	 * @return the edges2True
	 */
	public boolean edges2True() {
		return m_Edges2True;
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
	public Determinization determinization() {
		return m_Determiniation;
	}

	/**
	 * @return the difference
	 */
	public boolean differenceSenwa() {
		return m_Prefs.getBoolean(PreferenceInitializer.LABEL_DIFFERENCE_SENWA);
	}

	/**
	 * @return the minimize
	 */
	public boolean minimize() {
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
		return m_Prefs.getBoolean(PreferenceInitializer.LABEL_cutOff);
	}

	public boolean unfoldingToNet() {
		return m_Prefs.getBoolean(PreferenceInitializer.LABEL_unfolding2Net);
	}

	public String order() {
		return m_Prefs.getString(PreferenceInitializer.LABEL_Order);
	}

	public boolean SimplifyCodeBlocks() {
		return m_Prefs
				.getBoolean(PreferenceInitializer.LABEL_simplifyCodeBlocks);
	}

}
