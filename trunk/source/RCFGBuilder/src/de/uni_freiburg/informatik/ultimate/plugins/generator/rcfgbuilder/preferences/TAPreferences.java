package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences;

import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.Solver;


public class TAPreferences {

	
	private final boolean m_Interprocedural;
	private final int m_MaxIterations;
	private final int m_watchIteration;
	private final Artifact m_Artifact;
	private final InterpolatedLocs m_interpolatedLocs;
	private final boolean m_Edges2True;
	private final InterpolantAutomaton m_InterpolantAutomaton;
	private final boolean m_DumpFormulas;
	private final boolean m_DumpAutomata;
	private final String m_DumpPath;
	private final Determinization m_Determiniation;
	private final boolean m_Minimize;
	private final boolean m_Hoare;
	private final Concurrency m_Concurrency;
	private final boolean m_SeperateViolationCheck = true;
	private final boolean m_MainMode;
	private final String m_MainProcedure;
	private IEclipsePreferences m_Prefs;



	public enum Artifact { ABSTRACTION, INTERPOLANT_AUTOMATON, NEG_INTERPOLANT_AUTOMATON, RCFG }
	public enum InterpolatedLocs { ALL, CUTPOINTS, GUESS, WP }
	public enum InterpolantAutomaton { CANONICAL, TOTALINTERPOLATION, SINGLETRACE, TWOTRACK }
	public enum Determinization { POWERSET, BESTAPPROXIMATION, SELFLOOP, STRONGESTPOST, EAGERPOST, LAZYPOST }
	public enum Concurrency { FINITE_AUTOMATA, PETRI_NET }
	public enum Letter { STATEMENT, SEQUENCE, BLOCK }
	
	
	
	public TAPreferences() {
	
		ConfigurationScope scope = new ConfigurationScope();
		m_Prefs = scope.getNode(Activator.PLUGIN_ID);

		m_Interprocedural = m_Prefs.getBoolean(PreferenceValues.NAME_INTERPROCEDUTAL, PreferenceValues.DEF_INTERPROCEDUTAL);





		m_MaxIterations = m_Prefs.getInt(PreferenceValues.NAME_ITERATIONS, PreferenceValues.DEF_ITERATIONS);
		m_watchIteration = m_Prefs.getInt(PreferenceValues.NAME_WATCHITERATION, PreferenceValues.DEF_WATCHITERATION);

		String prefArtifactString = m_Prefs.get(PreferenceValues.NAME_ARTIFACT, PreferenceValues.DEF_ARTIFACT);
		
		
		if (prefArtifactString.equals(PreferenceValues.VALUE_INTERPOLANT_AUTOMATON)) {
			m_Artifact = Artifact.INTERPOLANT_AUTOMATON;
		}
		else if (prefArtifactString.equals(PreferenceValues.VALUE_NEG_INTERPOLANT_AUTOMATON)) {
			m_Artifact = Artifact.NEG_INTERPOLANT_AUTOMATON;
		}
		else if (prefArtifactString.equals(PreferenceValues.VALUE_ABSTRACTION)) {
			m_Artifact = Artifact.ABSTRACTION;
		}
		else if (prefArtifactString.equals(PreferenceValues.VALUE_RCFG)) {
			m_Artifact = Artifact.RCFG;
		}
		else {
			throw new IllegalArgumentException();
		}
		
		m_Hoare = m_Prefs.getBoolean(PreferenceValues.NAME_HOARE, PreferenceValues.DEF_HOARE);

		String prefInterpolants = m_Prefs.get(PreferenceValues.NAME_INTERPOLATED_LOCS, PreferenceValues.DEF_INTERPOLANTS);
		if (prefInterpolants.equals(PreferenceValues.VALUE_CUTPOINTS)) {
			m_interpolatedLocs = InterpolatedLocs.CUTPOINTS;
		}
		else if (prefInterpolants.equals(PreferenceValues.VALUE_ALL_LOC)) {
			m_interpolatedLocs = InterpolatedLocs.ALL;
		}
		else if (prefInterpolants.equals(PreferenceValues.VALUE_ITP_GUESS)) {
			m_interpolatedLocs = InterpolatedLocs.GUESS;
		}
		else if (prefInterpolants.equals(PreferenceValues.VALUE_ITP_WP)) {
			m_interpolatedLocs = InterpolatedLocs.WP;
		}
		else {
			throw new IllegalArgumentException();
		}


		m_Edges2True = m_Prefs.getBoolean(PreferenceValues.NAME_EDGES2TRUE, PreferenceValues.DEF_EDGES2TRUE);

		String prefAdditionalEdges = m_Prefs.get(PreferenceValues.NAME_InterpolantAutomaton, PreferenceValues.DEF_ADDITIONAL_EDGES);
		if (prefAdditionalEdges.equals(PreferenceValues.VALUE_InterpolantAutomaton_SingleTrace)) {
			m_InterpolantAutomaton = InterpolantAutomaton.SINGLETRACE;
		}
		else if (prefAdditionalEdges.equals(PreferenceValues.VALUE_InterpolantAutomaton_TwoTrack)) {
			m_InterpolantAutomaton = InterpolantAutomaton.TWOTRACK;
		}
		else if (prefAdditionalEdges.equals(PreferenceValues.VALUE_InterpolantAutomaton_Canonical)) {
			m_InterpolantAutomaton = InterpolantAutomaton.CANONICAL;
		}
		else if (prefAdditionalEdges.equals(PreferenceValues.VALUE_InterpolantAutomaton_TotalInterpolation)) {
			m_InterpolantAutomaton = InterpolantAutomaton.TOTALINTERPOLATION;
		}
		else {
			throw new IllegalArgumentException();
		}


		m_DumpFormulas = m_Prefs.getBoolean(PreferenceValues.NAME_DUMPFORMULAS, PreferenceValues.DEF_DUMPFORMULAS);
		m_DumpAutomata = m_Prefs.getBoolean(PreferenceValues.NAME_DUMPAUTOMATA, PreferenceValues.DEF_DUMPAUTOMATA);

		m_DumpPath = m_Prefs.get(PreferenceValues.NAME_DUMPPATH, PreferenceValues.DEF_DUMPPATH);

		String prefDeterminization = m_Prefs.get(PreferenceValues.NAME_DETERMINIZATION, PreferenceValues.DEF_DETERMINIZATION);
		if (prefDeterminization.equals(PreferenceValues.VALUE_POWERSET)) {
			m_Determiniation = Determinization.POWERSET;
		}
		else if (prefDeterminization.equals(PreferenceValues.VALUE_BESTAPPROXIMATION)) {
			m_Determiniation = Determinization.BESTAPPROXIMATION;
		}
		else if (prefDeterminization.equals(PreferenceValues.VALUE_SELFLOOP)) {
			m_Determiniation = Determinization.SELFLOOP;
		}
		else if (prefDeterminization.equals(PreferenceValues.VALUE_STRONGESTPOST)) {
			m_Determiniation = Determinization.STRONGESTPOST;
		}
		else if (prefDeterminization.equals(PreferenceValues.VALUE_EAGERPOST)) {
			m_Determiniation = Determinization.EAGERPOST;
		}
		else if (prefDeterminization.equals(PreferenceValues.VALUE_LAZYPOST)) {
			m_Determiniation = Determinization.LAZYPOST;
		}
		else {
			throw new IllegalArgumentException();
		}

		m_Minimize = m_Prefs.getBoolean(PreferenceValues.NAME_MINIMIZE, PreferenceValues.DEF_MINIMIZE);
	
		String prefConcurrency = m_Prefs.get(PreferenceValues.NAME_CONCURRENCY, PreferenceValues.DEF_CONCURRENCY);
		if (prefConcurrency.equals(PreferenceValues.VALUE_FINITE_AUTOMATON )) {
			m_Concurrency = Concurrency.FINITE_AUTOMATA;
		}
		else if (prefConcurrency.equals(PreferenceValues.VALUE_PETRI_NET )) {
			m_Concurrency = Concurrency.PETRI_NET;
		}
		else {
			throw new IllegalArgumentException();
		}
		
		if (artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON ) {
			throw new IllegalArgumentException("Show negated interpolant" +
					"automaton not possible when using difference.");
		}
		
		if ( m_watchIteration == 0 && 
				(artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON ||
				artifact() == Artifact.INTERPOLANT_AUTOMATON )) {
			throw new IllegalArgumentException("There is no interpolant" +
					"automaton in iteration 0.");
		}
		
		String mainProc = m_Prefs.get(PreferenceValues.NAME_MAINPROC, PreferenceValues.DEF_MAINPROC);
		if (mainProc.equals("")) {
			m_MainMode = false;
			m_MainProcedure = null;
		}
		else {
			m_MainMode = true;
			m_MainProcedure = mainProc;
		}
		
	}


	/**
	 * @return the interprocedural
	 */
	public boolean interprocedural() {
		return m_Interprocedural;
	}
	
	public boolean allErrorLocsAtOnce() {
		return m_Prefs.getBoolean(PreferenceValues.NAME_AllErrorsAtOnce, PreferenceValues.DEF_AllErrorsAtOnce);
	}
	
	
	public Letter letter() {
		String prefInterpolants = m_Prefs.get(PreferenceValues.NAME_LETTER, PreferenceValues.DEF_LETTER);
		if (prefInterpolants.equals(PreferenceValues.VALUE_LETTER_STATEMENT)) {
			return Letter.STATEMENT;
		} else if (prefInterpolants.equals(PreferenceValues.VALUE_LETTER_SEQUENCE)) {
			return Letter.SEQUENCE;
		} else if (prefInterpolants.equals(PreferenceValues.VALUE_LETTER_BLOCK)) {
			return Letter.BLOCK;
		} else {
			throw new IllegalArgumentException();
		}
	}


	/**
	 * @return the solver
	 */
	public Solver solver() {
		String prefSolverString = m_Prefs.get(PreferenceValues.NAME_SOLVER.toString(), PreferenceValues.DEF_SOLVER.toString());
		if (prefSolverString.equals(PreferenceValues.VALUE_SOLVER_SMTINTERPOL.toString())) {
			return PreferenceValues.VALUE_SOLVER_SMTINTERPOL;
		}
		else if (prefSolverString.equals(PreferenceValues.VALUE_SOLVER_Z3.toString())) {
			return PreferenceValues.VALUE_SOLVER_Z3;
		}
		else {
			throw new IllegalArgumentException();
		}

	}

	
	/**
	 * @return the timeout in seconds
	 */
	public int timeout() {
		int timeout = m_Prefs.getInt(PreferenceValues.NAME_TIMEOUT, PreferenceValues.DEF_TIMEOUT); 
		return timeout;
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
	public InterpolantAutomaton interpolantAutomaton() {
		return m_InterpolantAutomaton;
	}


	public boolean dumpScript() {
		return m_Prefs.getBoolean(PreferenceValues.NAME_DUMPSCRIPT, PreferenceValues.DEF_DUMPSCRIPT);
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
	public boolean differenceSenwa() {
		return m_Prefs.getBoolean(PreferenceValues.NAME_DIFFERENCE_SENWA, PreferenceValues.DEF_DIFFERENCE_SENWA);
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


	public boolean isMainMode() {
		return m_MainMode;
	}


	public String getMainProcedure() {
		return m_MainProcedure;
	}
	
	
	public boolean cutOffRequiresSameTransition() {
		return m_Prefs.getBoolean(PreferenceValues.NAME_cutOff, PreferenceValues.DEF_cutOff);
	}
	
	public boolean unfoldingToNet() {
		return m_Prefs.getBoolean(PreferenceValues.NAME_unfolding2Net, PreferenceValues.DEF_unfolding2Net);
	}
	
	public String order() {
		String prefOrderString = m_Prefs.get(PreferenceValues.NAME_Order, PreferenceValues.DEF_Order);
		return prefOrderString;
	}
	
	public boolean SimplifyCodeBlocks() {
		return m_Prefs.getBoolean(PreferenceValues.NAME_simplifyCodeBlocks, PreferenceValues.DEF_simplifyCodeBlocks);
	}
	
	public boolean PreserveGotoEdges() {
		return m_Prefs.getBoolean(PreferenceValues.NAME_PreserveGotoEdges, PreferenceValues.DEF_PreserveGotoEdges);
	}
	
	
	
}
