/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import org.apache.commons.cli.ParseException;

import de.uni_freiburg.informatik.ultimate.cli.CommandLineController;
import de.uni_freiburg.informatik.ultimate.cli.ParsedParameter;
import de.uni_freiburg.informatik.ultimate.cli.exceptions.InvalidFileArgumentException;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.DefaultPassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.PassRunner;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.UncheckedInterruptedException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.passes.HDDPass;

/**
 * Temporarily wraps a checked exceptions in a runtime exception to propagate it from the test predicate back to the
 * delta debugger controller.
 */
class CheckedExceptionWrapper extends RuntimeException {
	/**
	 *
	 */
	private static final long serialVersionUID = 1L;
	Exception cause;

	CheckedExceptionWrapper(final Exception cause) {
		this.cause = cause;
	}
}

/**
 * The delta debugger controller can repeat a defined toolchain until the specified input can not be reduced any
 * further.
 *
 * This is a quick and dirty implementation with some unfortunate limitations: Parallel testing is not possible, because
 * global state has to be used to associate the results/exception of a toolchain exceution. The test function which
 * defines the behaviour that has to be kept by the reduced variants is implemented right here in this class
 * isToolchainResultInteresting. No user interaction possible, final and intermediate output is written to the log.
 */
public class DeltaDebuggerController extends CommandLineController {

	private Optional<ToolchainException> mException;
	private Optional<Map<String, List<IResult>>> mResults;

	@Override
	public void displayException(final IToolchainData<RunDefinition> toolchain, final String description,
			final Throwable ex) {
		// super.displayException(toolchain, description, ex);

		mException = Optional.of(new ToolchainException(description, ex));
	}

	@Override
	public void displayToolchainResults(final IToolchainData<RunDefinition> toolchain,
			final Map<String, List<IResult>> results) {
		// super.displayToolchainResults(toolchain, results);

		// The copy is necessary, because otheriwse the map is empty after
		// executeToolchain returns?!?
		mResults = Optional.of(new HashMap<String, List<IResult>>(results));
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	/**
	 * Determines if the previous toolchain run showed the behvaiour of interest, i.e. the previous reduction was
	 * successful.
	 *
	 * Check the values stored in mException and mResults to access the previous results and/or exception.
	 *
	 * @return true iff the previous toolchain run showed the behvaiour of interest
	 */
	protected boolean isToolchainResultInteresting() {
		// Example test implementation for the NullPointerException caused by
		// the following toolchain/input;
		// - AbstractInterpretationC.xml
		// - examples/programs/regression/c/BugForLoop01.c
		// - ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT.epf

		// For some reason the exception is not reported via displayException
		// but inside the results map and direct access to the throwable is not
		// possible,
		// so strings have to be compared.
		final Optional<List<IResult>> expectedErrorResult = mResults
				.map(results -> results
						.get("de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2"))
				.filter(v -> v.size() == 1 && v.get(0) instanceof ExceptionOrErrorResult && v.toString().equals(
						"[de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2: NullPointerException: null: de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator$CheckForSubtreeInclusion.check(CACSL2BoogieBacktranslator.java:1176)]"));

		return expectedErrorResult.isPresent();
	}

	Optional<String> runDeltaDebuggerLoop(final ICore<RunDefinition> core, final ILogger logger,
			final IToolchainData<RunDefinition> toolchain, final String inputSource)
			throws ParseException, InvalidFileArgumentException, InterruptedException {
		final PassRunner runner = new PassRunner();
		runner.setContextFactory(DefaultPassContext::new);
		runner.setTestFunction(variant -> {
			logger.debug("testing variant\n-----------------------\n" + variant + "\n----------------------------\n");
			try {
				// Create a temporary file for this variant that can be passed
				// to the toolchain
				final File tempFile = File.createTempFile("ultimatedd-variant-", ".c");
				tempFile.deleteOnExit();
				Files.write(tempFile.toPath(), variant.getBytes(StandardCharsets.UTF_8));

				// Execute the toolchain and store the results in the global
				// controller state
				return runToolchainAndCheckResults(core, logger, toolchain, new File[] { tempFile });
			} catch (final Exception e) {
				throw new CheckedExceptionWrapper(e);
			}

		});

		runner.setPasses(HDDPass.DEFAULT);

		// No parallel testing is currently possible because global state is
		// used to store toolchain results/exception.
		// runner.enableParallelTesting(Executors.newFixedThreadPool(2), 2);

		// Run the delta debugger loop. Make sure to unwrap and rethrow
		// unhandled checked exceptions.
		try {
			return runner.run(inputSource);
		} catch (final CheckedExceptionWrapper e) {
			if (e.cause instanceof ParseException) {
				throw (ParseException) e.cause;
			}
			if (e.cause instanceof InvalidFileArgumentException) {
				throw (InvalidFileArgumentException) e.cause;
			}
			if (e.cause instanceof InterruptedException) {
				throw (InterruptedException) e.cause;
			}
			throw new RuntimeException(e.cause);
		} catch (final UncheckedInterruptedException e) {
			throw (InterruptedException) e.getCause();
		}

	}

	private boolean runToolchainAndCheckResults(final ICore<RunDefinition> core, final ILogger logger,
			final IToolchainData<RunDefinition> toolchain, final File[] inputFiles) throws InterruptedException {
		mException = Optional.empty();
		mResults = Optional.empty();
		executeToolchain(core, inputFiles, logger, toolchain);
		return isToolchainResultInteresting();
	}

	@Override
	protected void startExecutingToolchain(final ICore<RunDefinition> core, final ParsedParameter cliParams,
			final ILogger logger, final IToolchainData<RunDefinition> toolchain)
			throws ParseException, InvalidFileArgumentException, InterruptedException {
		final File[] initialInputFiles = cliParams.getInputFiles();

		// The Delta Debugger only reduces a single source string, so only a
		// single input file is supported right now.
		if (initialInputFiles.length != 1) {
			// TODO: If multiple input files are supposed to be supported, the
			// main source file to be reduced has to be selected in some way.
			throw new InvalidFileArgumentException("only single input file supported by current implementation");
		}

		String inputSource;
		try {
			inputSource = new String(Files.readAllBytes(initialInputFiles[0].toPath()), StandardCharsets.UTF_8);
		} catch (final IOException e) {
			throw new InvalidFileArgumentException("error reading input source file", e);
		}

		// Optional: Verify that the unmodified input shows the behaviour of
		// interest
		if (!runToolchainAndCheckResults(core, logger, toolchain, initialInputFiles)) {
			// TODO: replace by proper way to report this error to the user
			throw new InvalidFileArgumentException("The initial input does not show the behaviour of interest");
		}

		final Optional<String> reducedResult = runDeltaDebuggerLoop(core, logger, toolchain, inputSource);

		logger.warn("\n------------------------------------\n");
		logger.warn(reducedResult.orElse("[No reduction possible]"));
		logger.warn("\n------------------------------------\n");
	}
}

/**
 * Stores arguments to displayException()
 */
class ToolchainException {
	public final String description;

	public final Throwable exception;

	public ToolchainException(final String description, final Throwable exception) {
		super();
		this.description = description;
		this.exception = exception;
	}
}
