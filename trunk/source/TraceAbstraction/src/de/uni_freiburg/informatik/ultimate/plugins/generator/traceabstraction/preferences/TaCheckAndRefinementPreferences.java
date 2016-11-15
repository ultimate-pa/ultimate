/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceCheckAndRefinementSelection;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;

/**
 * Wrapper for preferences of trace check and refinement selection module.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class TaCheckAndRefinementPreferences {
	/**
	 * Policy how to choose the setting in {@link TraceCheckAndRefinementSelection}.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum TaCheckAndRefinementSettingPolicy {
		/**
		 * Chooses the settings in the list order.
		 */
		SEQUENTIAL
	}
	
	/**
	 * Policy how to choose the interpolant automaton in {@link TraceCheckAndRefinementSelection}.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum TaInterpolantAutomatonConstructionPolicy {
		/**
		 * Uses the first interpolant automaton that is accepted. If none is accepted, the best automaton is used. Ties
		 * are broken for the first result in the sequence.
		 */
		FIRST_BEST
	}
	
	private final InterpolationTechnique mInterpolationTechnique;
	
	private final boolean mUseSeparateSolverForTracechecks;
	private final SolverMode mSolverMode;
	private final boolean mFakeNonIncrementalSolver;
	private final String mCommandExternalSolver;
	private final boolean mDumpSmtScriptToFile;
	private final String mPathOfDumpedScript;
	private final String mLogicForExternalSolver;
	
	private final AssertCodeBlockOrder mAssertCodeBlocksIncrementally;
	private final UnsatCores mUnsatCores;
	private final boolean mUseLiveVariables;
	private final boolean mUseInterpolantConsolidation;
	private final boolean mUseNonlinearConstraints;
	private final boolean mUseVarsFromUnsatCore;
	
	/**
	 * Constructor from existing trace abstraction and Ultimate preferences.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param taPrefs
	 *            trace abstraction preferences
	 * @param interpolationTechnique
	 *            interpolation technique
	 */
	public TaCheckAndRefinementPreferences(final IUltimateServiceProvider services, final TAPreferences taPrefs,
			final InterpolationTechnique interpolationTechnique) {
		mInterpolationTechnique = interpolationTechnique;
		
		mUseSeparateSolverForTracechecks = taPrefs.useSeparateSolverForTracechecks();
		mSolverMode = taPrefs.solverMode();
		mFakeNonIncrementalSolver = taPrefs.fakeNonIncrementalSolver();
		mCommandExternalSolver = taPrefs.commandExternalSolver();
		mDumpSmtScriptToFile = taPrefs.dumpSmtScriptToFile();
		mPathOfDumpedScript = taPrefs.pathOfDumpedScript();
		mLogicForExternalSolver = taPrefs.logicForExternalSolver();
		
		final IPreferenceProvider ultimatePrefs = services.getPreferenceProvider(Activator.PLUGIN_ID);
		mAssertCodeBlocksIncrementally =
				ultimatePrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ASSERT_CODEBLOCKS_INCREMENTALLY,
						AssertCodeBlockOrder.class);
		mUnsatCores = ultimatePrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_UNSAT_CORES, UnsatCores.class);
		mUseLiveVariables = ultimatePrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_LIVE_VARIABLES);
		mUseInterpolantConsolidation =
				ultimatePrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANTS_CONSOLIDATION);
		mUseNonlinearConstraints = ultimatePrefs
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_NONLINEAR_CONSTRAINTS_IN_PATHINVARIANTS);
		mUseVarsFromUnsatCore =
				ultimatePrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_UNSAT_CORES_IN_PATHINVARIANTS);
	}
	
	public boolean getUseSeparateSolverForTracechecks() {
		return mUseSeparateSolverForTracechecks;
	}
	
	public SolverMode getSolverMode() {
		return mSolverMode;
	}
	
	public boolean getFakeNonIncrementalSolver() {
		return mFakeNonIncrementalSolver;
	}
	
	public String getCommandExternalSolver() {
		return mCommandExternalSolver;
	}
	
	public boolean getDumpSmtScriptToFile() {
		return mDumpSmtScriptToFile;
	}
	
	public String getPathOfDumpedScript() {
		return mPathOfDumpedScript;
	}
	
	public String getLogicForExternalSolver() {
		return mLogicForExternalSolver;
	}
	
	public InterpolationTechnique getInterpolationTechnique() {
		return mInterpolationTechnique;
	}
	
	public AssertCodeBlockOrder getAssertCodeBlocksIncrementally() {
		return mAssertCodeBlocksIncrementally;
	}
	
	public UnsatCores getUnsatCores() {
		return mUnsatCores;
	}
	
	public boolean getUseLiveVariables() {
		return mUseLiveVariables;
	}
	
	public boolean getUseInterpolantConsolidation() {
		return mUseInterpolantConsolidation;
	}
	
	public boolean getUseNonlinearConstraints() {
		return mUseNonlinearConstraints;
	}
	
	public boolean getUseVarsFromUnsatCore() {
		return mUseVarsFromUnsatCore;
	}
}
