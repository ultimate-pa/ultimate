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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramDumper.InputMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class PathProgramDumpController<LETTER extends IIcfgTransition<?>> {

	private enum DumpStop {
		NEVER, AFTER_FIRST_DUMP, BEFORE_FIRST_DUPLICATE
	}

	private static final int DUMP_PATH_PROGRAMS_THAT_EXCEED_TRACE_HIST_MAX_THRESHOLD = Integer.MAX_VALUE;
	private static final DumpStop STOP_AFTER_FIRST_PATH_PROGRAM_WAS_DUMPED = DumpStop.BEFORE_FIRST_DUPLICATE;
	private static final InputMode DUMP_PATH_PROGRAMS_INPUT_MODE = InputMode.ICFG;

	private final IUltimateServiceProvider mServices;
	private final TAPreferences mPref;
	private final IIcfg<?> mIcfg;
	private final Set<Set<LETTER>> mAlreadyDumped = new HashSet<>();

	public PathProgramDumpController(final IUltimateServiceProvider services, final TAPreferences pref,
			final IIcfg<?> icfgContainer) {
		mServices = services;
		mPref = pref;
		mIcfg = icfgContainer;
	}

	public void reportPathProgram(final NestedRun<LETTER, IPredicate> counterexample,
			final boolean perfectInterpolatSequenceFound, final int iteration) {
		if (!perfectInterpolatSequenceFound) {
			announceDump(counterexample, iteration);
			doDump(counterexample, iteration);
		} else if (DUMP_PATH_PROGRAMS_THAT_EXCEED_TRACE_HIST_MAX_THRESHOLD != Integer.MAX_VALUE) {
			announceDump(counterexample, iteration);
			final HistogramOfIterable<LETTER> traceHistogram =
					new HistogramOfIterable<LETTER>(counterexample.getWord());
			if (traceHistogram.getMax() > DUMP_PATH_PROGRAMS_THAT_EXCEED_TRACE_HIST_MAX_THRESHOLD) {
				final String filename =
						mPref.dumpPath() + File.separator + mIcfg.getIdentifier() + "_" + iteration + ".bpl";
				new PathProgramDumper(mIcfg, mServices, counterexample, filename, DUMP_PATH_PROGRAMS_INPUT_MODE);
				if (STOP_AFTER_FIRST_PATH_PROGRAM_WAS_DUMPED == DumpStop.AFTER_FIRST_DUMP) {
					final String message = "dumped path program with trace histogram max " + traceHistogram.getMax();
					final String taskDescription = "trying to verify (iteration " + iteration + ")";
					throw new ToolchainCanceledException(message, getClass(), taskDescription);
				}
			}
		}
	}

	private void announceDump(final NestedRun<LETTER, IPredicate> counterexample, final int iteration) {
		final Set<LETTER> letters = new HashSet<>(counterexample.getWord().asList());
		final boolean wasNew = mAlreadyDumped.add(letters);
		if (!wasNew) {
			final String message = "stopped before dumping similar path program twice";
			final String taskDescription = "trying to verify (iteration " + iteration + ")";
			throw new ToolchainCanceledException(message, getClass(), taskDescription);
		}

	}

	private void doDump(final NestedRun<? extends IAction, IPredicate> counterexample, final int iteration) {
		final String filename = mPref.dumpPath() + File.separator + mIcfg.getIdentifier() + "_" + iteration + ".bpl";
		new PathProgramDumper(mIcfg, mServices, counterexample, filename, DUMP_PATH_PROGRAMS_INPUT_MODE);
		if (STOP_AFTER_FIRST_PATH_PROGRAM_WAS_DUMPED == DumpStop.AFTER_FIRST_DUMP) {
			final String message = "dumped path program for which we did not find perfect sequence of interpolants";
			final String taskDescription = "trying to verify (iteration " + iteration + ")";
			throw new ToolchainCanceledException(message, getClass(), taskDescription);
		}
	}
}
