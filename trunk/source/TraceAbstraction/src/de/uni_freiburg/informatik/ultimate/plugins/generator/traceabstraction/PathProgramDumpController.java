/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.io.File;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramDumper.InputMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.PathProgramDumpStop;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class PathProgramDumpController<L extends IIcfgTransition<?>> {

	private static final InputMode DUMP_PATH_PROGRAMS_INPUT_MODE = InputMode.ICFG;

	private final IUltimateServiceProvider mServices;
	private final TAPreferences mPref;
	private final IIcfg<?> mIcfg;
	private final Set<Set<L>> mAlreadyDumped = new HashSet<>();
	private final boolean mEnabled;
	private final boolean mDumpIfNotPerfect;
	private final int mDumpIfAnalyzedTooOften;
	private final PathProgramDumpStop mDumpStopMode;

	public PathProgramDumpController(final IUltimateServiceProvider services, final TAPreferences pref,
			final IIcfg<?> icfgContainer) {
		mServices = services;
		mPref = pref;
		mIcfg = icfgContainer;

		mDumpIfNotPerfect = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_DUMP_PATH_PROGRAM_IF_NOT_PERFECT);
		mDumpIfAnalyzedTooOften = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getInt(TraceAbstractionPreferenceInitializer.LABEL_DUMP_PATH_PROGRAM_IF_ANALYZED_TOO_OFTEN);

		mEnabled = mDumpIfNotPerfect || mDumpIfAnalyzedTooOften > 0;

		mDumpStopMode = services.getPreferenceProvider(Activator.PLUGIN_ID).getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_DUMP_PATH_PROGRAM_STOP_MODE, PathProgramDumpStop.class);

	}

	public void reportPathProgram(final IRun<L, ?> cex, final boolean somePerfectSequenceFound, final int iteration) {
		if (shouldDumpPathProgram(somePerfectSequenceFound, cex)) {
			doDump(cex, iteration);
		}
	}

	private boolean shouldDumpPathProgram(final boolean perfectInterpolatSequenceFound,
			final IRun<L, ?> counterexample) {
		if (!mEnabled) {
			return false;
		}
		if (mDumpIfNotPerfect && !perfectInterpolatSequenceFound) {
			return true;
		}
		if (mDumpIfAnalyzedTooOften > 0) {
			final HistogramOfIterable<L> traceHistogram = new HistogramOfIterable<>(counterexample.getWord());
			return traceHistogram.getMax() > mDumpIfAnalyzedTooOften;
		}
		return false;
	}

	private void doDump(final IRun<L, ?> counterexample, final int iteration) {
		final boolean wasNew = mAlreadyDumped.add(new HashSet<>(counterexample.getWord().asList()));
		if (mDumpStopMode == PathProgramDumpStop.BEFORE_FIRST_DUPLICATE && !wasNew) {
			final String message = "stopped before dumping similar path program twice";
			throw createToolchainCanceledException(message, iteration);
		}

		final String filename = mPref.dumpPath() + File.separator + mIcfg.getIdentifier() + "_" + iteration + ".bpl";
		new PathProgramDumper(mIcfg, mServices, counterexample, filename, DUMP_PATH_PROGRAMS_INPUT_MODE);

		if (mDumpStopMode == PathProgramDumpStop.AFTER_FIRST_DUMP) {
			final String message = "stopping after dumping path program";
			throw createToolchainCanceledException(message, iteration);
		}
	}

	private ToolchainCanceledException createToolchainCanceledException(final String message, final int iteration) {
		final String taskDescription = "trying to verify (iteration " + iteration + ")";
		return new ToolchainCanceledException(message, getClass(), taskDescription);
	}

}
