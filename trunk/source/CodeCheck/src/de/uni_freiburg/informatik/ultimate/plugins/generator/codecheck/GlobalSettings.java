package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.Checker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.EdgeCheckOptimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.PredicateUnification;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.SolverAndInterpolator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;

public class GlobalSettings {
	
	public static GlobalSettings _instance;
	
		//default configuration
//	String m_dotGraphPath = "C:/temp/codeCheckGraphs";
	
	
//    boolean svcomp2014Mode = false; //TODO: this is only hardcoded??
//    boolean svcomp2014Mode = true;
	public String _dotGraphPath = "";
//	String _dotGraphPath = "C:/temp/codeCheckGraphs";
//	SolverAndInterpolator _solverAndInterpolator = SolverAndInterpolator.SMTINTERPOL;
	public SolverAndInterpolator _solverAndInterpolator = SolverAndInterpolator.Z3SPWP;
//	INTERPOLATION _interpolationMode = INTERPOLATION.Craig_TreeInterpolation;
	public INTERPOLATION _interpolationMode = INTERPOLATION.ForwardPredicates;
	public PredicateUnification _predicateUnification = PredicateUnification.PER_VERIFICATION;
	public EdgeCheckOptimization _edgeCheckOptimization = EdgeCheckOptimization.NONE;
	public Checker checker = Checker.ULTIMATE;
//	boolean _checkOnlyMain = false;
	public boolean _memoizeNormalEdgeChecks = true;
	public boolean _memoizeReturnEdgeChecks = true;

	public static void init() {
		_instance = new GlobalSettings();
	}

	public GlobalSettings() {
	}

}
