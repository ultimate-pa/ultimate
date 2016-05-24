package de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.script;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.preferences.HornClauseGraphBuilderPreferenceInitializer;

public class HCGBuilderHelper {
	
	public static class ConstructAndInitializeBackendSmtSolver {
	
		private Settings mSolverSettings;
		private String mLogicForExternalSolver;
		private Script mScript;

		public ConstructAndInitializeBackendSmtSolver(IUltimateServiceProvider services, 
				IToolchainStorage storage,
				String filename) {
			constructAndInitializeBackendSmtSolver(services, storage, filename);
		}

		void constructAndInitializeBackendSmtSolver(
				IUltimateServiceProvider services, 
				IToolchainStorage storage,
				String filename) {
			final SolverMode solverMode = (new RcpPreferenceProvider(Activator.PLUGIN_ID))
					.getEnum(HornClauseGraphBuilderPreferenceInitializer.LABEL_Solver, SolverMode.class);

			final String commandExternalSolver = (new RcpPreferenceProvider(Activator.PLUGIN_ID))
					.getString(HornClauseGraphBuilderPreferenceInitializer.LABEL_ExtSolverCommand);

			mLogicForExternalSolver = (new RcpPreferenceProvider(Activator.PLUGIN_ID))
					.getString(HornClauseGraphBuilderPreferenceInitializer.LABEL_ExtSolverLogic);

			mSolverSettings = SolverBuilder.constructSolverSettings(
					filename, solverMode, commandExternalSolver, false, null);

			mScript =  SolverBuilder.buildAndInitializeSolver(services, 
					storage, 
					solverMode, 
					mSolverSettings, 
					//				dumpUsatCoreTrackBenchmark, 
					false, 
					//				dumpMainTrackBenchmark,
					false,
					mLogicForExternalSolver, 
					"HornClauseSolverBackendSolverScript");		
		}

		public Settings getSolverSettings() {
			return mSolverSettings;
		}

		public String getLogicForExternalSolver() {
			return mLogicForExternalSolver;
		}

		public Script getScript() {
			return mScript;
		}
	}
}
