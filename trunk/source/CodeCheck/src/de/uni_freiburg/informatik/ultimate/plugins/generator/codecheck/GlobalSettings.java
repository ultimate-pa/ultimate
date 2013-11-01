package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.PreferenceValues.EdgeCheckOptimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.PreferenceValues.PredicateUnification;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.PreferenceValues.SolverAndInterpolator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.INTERPOLATION;

public class GlobalSettings {
	
	static GlobalSettings _instance;
	
		//default configuration
//	String m_dotGraphPath = "C:/temp/codeCheckGraphs";
	
	
    boolean svcomp2014Mode = true;
	String _dotGraphPath = "";
//	String _dotGraphPath = "C:/temp/codeCheckGraphs";
	SolverAndInterpolator _solverAndInterpolator = SolverAndInterpolator.SMTINTERPOL;
	INTERPOLATION _interpolationMode = INTERPOLATION.Craig_TreeInterpolation;
	PredicateUnification _predicateUnification = PredicateUnification.PER_VERIFICATION;
	EdgeCheckOptimization _edgeCheckOptimization = EdgeCheckOptimization.NONE;
	Checker checker = Checker.ULTIMATE;
	boolean _checkOnlyMain = false;
	boolean _memoizeNormalEdgeChecks = true;
	boolean _memoizeReturnEdgeChecks = true;

	public static void init() {
		_instance = new GlobalSettings();
	}

	public GlobalSettings() {
	}

}
