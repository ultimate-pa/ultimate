package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.parsing;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.preferences.TreeAutomizerPreferenceInitializer;

public class HCGBuilderHelper {

	public static class ConstructAndInitializeBackendSmtSolver {

		private Settings mSolverSettings;
		private String mLogicForExternalSolver;
		private ManagedScript mScript;

		public ConstructAndInitializeBackendSmtSolver(final IUltimateServiceProvider services,
				final IToolchainStorage storage,
				final String filename) {
			constructAndInitializeBackendSmtSolver(services, storage, filename);
		}

		void constructAndInitializeBackendSmtSolver(
				final IUltimateServiceProvider services,
				final IToolchainStorage storage,
				final String filename) {
			final IPreferenceProvider prefs = services.getPreferenceProvider(Activator.PLUGIN_ID);
			final SolverMode solverMode = prefs
					.getEnum(TreeAutomizerPreferenceInitializer.LABEL_Solver, SolverMode.class);

			final String commandExternalSolver = prefs
					.getString(TreeAutomizerPreferenceInitializer.LABEL_ExtSolverCommand);

			mLogicForExternalSolver = prefs
					.getString(TreeAutomizerPreferenceInitializer.LABEL_ExtSolverLogic);

			final boolean fakeNonIncrementalSolver = false;
			mSolverSettings = SolverBuilder.constructSolverSettings(
					filename, solverMode, fakeNonIncrementalSolver , 
					commandExternalSolver, false, null);

			final Script script = SolverBuilder.buildAndInitializeSolver(services,
					storage,
					solverMode,
					mSolverSettings,
					// dumpUsatCoreTrackBenchmark,
					false,
					// dumpMainTrackBenchmark,
					false,
					mLogicForExternalSolver,
					"HornClauseSolverBackendSolverScript");
			
			mScript = new ManagedScript(services, script);
		}

		public Settings getSolverSettings() {
			return mSolverSettings;
		}

		public String getLogicForExternalSolver() {
			return mLogicForExternalSolver;
		}

		public ManagedScript getScript() {
			return mScript;
		}
	}
}
