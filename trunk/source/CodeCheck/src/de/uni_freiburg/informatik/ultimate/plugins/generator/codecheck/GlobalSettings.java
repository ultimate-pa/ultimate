/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Mostafa Mahmoud Amin
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CodeCheck plug-in.
 * 
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.Checker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.EdgeCheckOptimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.PredicateUnification;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.RedirectionStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;

public class GlobalSettings {
	
	public static GlobalSettings _instance;
	
		//default configuration
//	String mdotGraphPath = "C:/temp/codeCheckGraphs";
	
	
//    boolean svcomp2014Mode = false; //TODO: this is only hardcoded??
//    boolean svcomp2014Mode = true;
	public String _dotGraphPath = "";
//	String _dotGraphPath = "C:/temp/codeCheckGraphs";
//	SolverAndInterpolator _solverAndInterpolator = SolverAndInterpolator.SMTINTERPOL;
//	public SolverAndInterpolator _solverAndInterpolator = SolverAndInterpolator.Z3SPWP;
//	InterpolationTechnique _interpolationMode = InterpolationTechnique.Craig_TreeInterpolation;
	public InterpolationTechnique _interpolationMode = InterpolationTechnique.ForwardPredicates;
	public PredicateUnification _predicateUnification = PredicateUnification.PER_VERIFICATION;
	public EdgeCheckOptimization _edgeCheckOptimization = EdgeCheckOptimization.NONE;
	public Checker checker = Checker.ULTIMATE;
//	boolean _checkOnlyMain = false;
	public boolean _memoizeNormalEdgeChecks = true;
	public boolean _memoizeReturnEdgeChecks = true;
	public int _iterations = -1;
	public RedirectionStrategy redirectionStrategy = RedirectionStrategy.No_Strategy;
	
	public boolean defaultRedirection = true;
	
	public boolean removeFalseNodes = false;
	
	public boolean checkSatisfiability = false;
	
	public boolean useInterpolantconsolidation = true;

	public boolean useSeparateSolverForTracechecks = true;

	public SolverMode chooseSeparateSolverForTracechecks;

	public String separateSolverForTracechecksCommand;

	public String separateSolverForTracechecksTheory;

	public boolean useLiveVariables;

	public UnsatCores useUnsatCores;

	public boolean useFallbackForSeparateSolverForTracechecks;

	public static void init() {
		_instance = new GlobalSettings();
	}
}
