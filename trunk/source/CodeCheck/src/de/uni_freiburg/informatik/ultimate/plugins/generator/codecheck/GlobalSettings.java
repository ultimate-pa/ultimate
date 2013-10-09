package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.PreferenceValues.EdgeCheckOptimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.PreferenceValues.PredicateUnification;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.INTERPOLATION;

public class GlobalSettings {

	public static de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.PreferenceValues.SolverAndInterpolator _solverAndInterpolator = null;
	public static GlobalSettings _instance;
	public boolean _memoizeNormalEdgeChecks;
	public PredicateUnification _predicateUnification;
	public boolean _memoizeReturnEdgeChecks;
	public EdgeCheckOptimization _edgeCheckOptimization;
	public boolean _checkOnlyMain;
	public INTERPOLATION _interpolationMode;
	public String _dotGraphPath;
	public Checker checker;
	
	public enum SolverAndInterpolator { SMTINTERPOL, Z3SPWP };
	public static void init() {
		// TODO Auto-generated method stub
		
	}

}
