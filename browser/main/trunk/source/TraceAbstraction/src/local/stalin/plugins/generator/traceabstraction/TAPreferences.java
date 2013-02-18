package local.stalin.plugins.generator.traceabstraction;

import local.stalin.SMTInterface.SMTInterface;
import local.stalin.plugins.generator.traceabstraction.preferences.PreferenceValues;

import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

public class TAPreferences {

	
	private final boolean m_Interprocedural;
	private final int m_Solver;
	private final int m_MaxIterations;
	private final int m_watchIteration;
	private final Artifact m_Artifact;
	private final InterpolatedLocs m_interpolatedLocs;
	private final boolean m_Edges2True;
	private final AdditionalEdges m_AdditionalEdges;
	private final boolean m_DumpFormulas;
	private final boolean m_DumpAutomata;
	private final String m_DumpPath;
	private final Determinization m_Determiniation;
	private final boolean m_Difference;
	private final boolean m_Minimize;

	private boolean m_Hoare = false;


	public enum Artifact { ABSTRACTION, INTERPOLANT_AUTOMATON, NEG_INTERPOLANT_AUTOMATON, RCFG }
	public enum InterpolatedLocs { ALL, CUTPOINTS }
	public enum AdditionalEdges { CANONICAL, EAGER, NONE }
	public enum Determinization { POWERSET, BESTAPPROXIMATION, SELFLOOP }
	
	
	public TAPreferences(String prefsID) {
	
		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode(Activator.s_PLUGIN_ID);

		m_Interprocedural = prefs.getBoolean(PreferenceValues.NAME_INTERPROCEDUTAL, PreferenceValues.DEF_INTERPROCEDUTAL);

		String prefSolverString = prefs.get(PreferenceValues.NAME_SOLVER, PreferenceValues.DEF_SOLVER);
		if (prefSolverString.equals(PreferenceValues.VALUE_SOLVER_SMTINTERPOL)) {
			m_Solver = SMTInterface.SOLVER_SMTINTERPOL;
		}
		else if (prefSolverString.equals(PreferenceValues.VALUE_SOLVER_GROUNDIFY)) {
			m_Solver = SMTInterface.SOLVER_GROUNDIFY;
		}
		else {
			throw new IllegalArgumentException();
		}

		m_MaxIterations = prefs.getInt(PreferenceValues.NAME_ITERATIONS, PreferenceValues.DEF_ITERATIONS);
		m_watchIteration = prefs.getInt(PreferenceValues.NAME_WATCHITERATION, PreferenceValues.DEF_WATCHITERATION);

		String prefArtifactString = prefs.get(PreferenceValues.NAME_ARTIFACT, PreferenceValues.DEF_ARTIFACT);
		if (prefArtifactString.equals(PreferenceValues.VALUE_INTERPOLANT_AUTOMATON)) {
			m_Artifact = Artifact.INTERPOLANT_AUTOMATON;
		}
		else if (prefArtifactString.equals(PreferenceValues.VALUE_NEG_INTERPOLANT_AUTOMATON)) {
			m_Artifact = Artifact.NEG_INTERPOLANT_AUTOMATON;
			m_Hoare = true;
		}
		else if (prefArtifactString.equals(PreferenceValues.VALUE_ABSTRACTION)) {
			m_Artifact = Artifact.ABSTRACTION;
			m_Hoare = true;
		}
		else if (prefArtifactString.equals(PreferenceValues.VALUE_RCFG)) {
			m_Artifact = Artifact.RCFG;
			m_Hoare = true;
		}
		else {
			throw new IllegalArgumentException();
		}

		String prefInterpolants = prefs.get(PreferenceValues.NAME_INTERPOLATED_LOCS, PreferenceValues.DEF_INTERPOLANTS);
		if (prefInterpolants.equals(PreferenceValues.VALUE_CUTPOINTS)) {
			m_interpolatedLocs = InterpolatedLocs.CUTPOINTS;
		}
		else if (prefInterpolants.equals(PreferenceValues.VALUE_ALL_LOC)) {
			m_interpolatedLocs = InterpolatedLocs.ALL;
		}
		else {
			throw new IllegalArgumentException();
		}


		m_Edges2True = prefs.getBoolean(PreferenceValues.NAME_EDGES2TRUE, PreferenceValues.DEF_EDGES2TRUE);

		String prefAdditionalEdges = prefs.get(PreferenceValues.NAME_ADDITIONAL_EDGES, PreferenceValues.DEF_ADDITIONAL_EDGES);
		if (prefAdditionalEdges.equals(PreferenceValues.VALUE_NO_EDGE)) {
			m_AdditionalEdges = AdditionalEdges.NONE;
		}
		else if (prefAdditionalEdges.equals(PreferenceValues.VALUE_CANONICAL)) {
			m_AdditionalEdges = AdditionalEdges.CANONICAL;
		}
		else if (prefAdditionalEdges.equals(PreferenceValues.VALUE_EAGER)) {
			m_AdditionalEdges = AdditionalEdges.EAGER;
		}
		else {
			throw new IllegalArgumentException();
		}


		m_DumpFormulas = prefs.getBoolean(PreferenceValues.NAME_DUMPFORMULAS, PreferenceValues.DEF_DUMPFORMULAS);
		m_DumpAutomata = prefs.getBoolean(PreferenceValues.NAME_DUMPAUTOMATA, PreferenceValues.DEF_DUMPAUTOMATA);

		m_DumpPath = prefs.get(PreferenceValues.NAME_DUMPPATH, PreferenceValues.DEF_DUMPPATH);

		String prefDeterminization = prefs.get(PreferenceValues.NAME_DETERMINIZATION, PreferenceValues.DEF_DETERMINIZATION);
		if (prefDeterminization.equals(PreferenceValues.VALUE_POWERSET)) {
			m_Determiniation = Determinization.POWERSET;
		}
		else if (prefDeterminization.equals(PreferenceValues.VALUE_BESTAPPROXIMATION)) {
			m_Determiniation = Determinization.BESTAPPROXIMATION;
		}
		else if (prefDeterminization.equals(PreferenceValues.VALUE_SELFLOOP)) {
			m_Determiniation = Determinization.SELFLOOP;
		}
		else {
			throw new IllegalArgumentException();
		}

		m_Difference = prefs.getBoolean(PreferenceValues.NAME_DIFFERENCE, PreferenceValues.DEF_DIFFERENCE);

		m_Minimize = prefs.getBoolean(PreferenceValues.NAME_MINIMIZE, PreferenceValues.DEF_MINIMIZE);
	
		
		
		if (artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON && 
				m_Difference) {
			throw new IllegalArgumentException("Show negated interpolant" +
					"automaton not possible when using difference.");
		}
		
		if (m_AdditionalEdges == AdditionalEdges.EAGER) {
			throw new IllegalArgumentException("Construction of eager" +
					" automaton not implemented, use BestApproximaion" +
					" determinization instead");
		}
		
		if ( m_watchIteration == 0 && 
				(artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON ||
				artifact() == Artifact.INTERPOLANT_AUTOMATON )) {
			throw new IllegalArgumentException("There is no interpolant" +
					"automaton in iteration 0.");
		}
	}


	/**
	 * @return the interprocedural
	 */
	public boolean interprocedural() {
		return m_Interprocedural;
	}


	/**
	 * @return the solver
	 */
	public int solver() {
		return m_Solver;
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
	public InterpolatedLocs interpolatedLocs() {
		return m_interpolatedLocs;
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
	public AdditionalEdges additionalEdges() {
		return m_AdditionalEdges;
	}


	/**
	 * @return the dumpFormulas
	 */
	public boolean dumpFormulas() {
		return m_DumpFormulas;
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
	public boolean difference() {
		return m_Difference;
	}


	/**
	 * @return the minimize
	 */
	public boolean minimize() {
		return m_Minimize;
	}


	public boolean computeHoareAnnotation() {
		return m_Hoare;
	}
	
	
	
	
	
	
	
	
}
