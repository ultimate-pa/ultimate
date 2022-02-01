/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TreeAutomizer Plugin.
 *
 * The ULTIMATE TreeAutomizer Plugin is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TreeAutomizer Plugin is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TreeAutomizer Plugin. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TreeAutomizer Plugin, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TreeAutomizer Plugin grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.source.smtparser.chc;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.source.smtparser.Activator;
import de.uni_freiburg.informatik.ultimate.source.smtparser.SmtParserPreferenceInitializer;

/**
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HCGBuilderHelper {

	public static class ConstructAndInitializeBackendSmtSolver {

		private final SolverSettings mSolverSettings;
		private final Logics mLogicForExternalSolver;
		private final ManagedScript mScript;

		public ConstructAndInitializeBackendSmtSolver(final IUltimateServiceProvider services, final String filename) {
			final IPreferenceProvider prefs = services.getPreferenceProvider(Activator.PLUGIN_ID);
			final SolverMode solverMode = prefs.getEnum(SmtParserPreferenceInitializer.LABEL_Solver, SolverMode.class);

			final String commandExternalSolver =
					prefs.getString(SmtParserPreferenceInitializer.LABEL_EXTERNAL_SOLVER_COMMAND);

			mLogicForExternalSolver =
					Logics.valueOf(prefs.getString(SmtParserPreferenceInitializer.LABEL_ExtSolverLogic));

			final String dumpPath = prefs.getString(SmtParserPreferenceInitializer.LABEL_SMT_DUMP_PATH);
			final boolean dumpScript = !dumpPath.isEmpty();

			final boolean fakeNonIncrementalSolver = false;
			final SolverSettings settings = SolverBuilder.constructSolverSettings().setSolverMode(solverMode)
					.setUseFakeIncrementalScript(fakeNonIncrementalSolver)
					.setDumpSmtScriptToFile(dumpScript, dumpPath, filename, false);

			if (solverMode.isExternal()) {
				mSolverSettings = settings.setUseExternalSolver(true, commandExternalSolver, mLogicForExternalSolver);
			} else {
				mSolverSettings = settings;
			}

			final Script script = SolverBuilder.buildAndInitializeSolver(services, mSolverSettings,
					"HornClauseSolverBackendSolverScript");

			mScript = new ManagedScript(services, script);
		}

		public SolverSettings getSolverSettings() {
			return mSolverSettings;
		}

		public Logics getLogicForExternalSolver() {
			return mLogicForExternalSolver;
		}

		public ManagedScript getScript() {
			return mScript;
		}
	}
}
