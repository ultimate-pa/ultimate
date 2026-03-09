package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ExecutionProducer.PartialExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramExecutions.ExecutionTermintionReason;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.IcfgInterpreterPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.IcfgInterpreterPreferences.OutputMethod;

public class IcfgInterpreterObserver extends BaseObserver {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private IIcfg<? extends IcfgLocation> mIcfg;
	private Map<ExecutionTermintionReason, List<PartialExecution>> mExecutions = new HashMap<>();
	private List<PartialExecution> mAggregateExecutions;
	private OutputMethod outputMethod;

	private Map<ExecutionTermintionReason, File> outputDirs;
	private Map<ExecutionTermintionReason, Integer> terminationCount;
	private Map<IcfgLocation, IResult> mFinalResults;
	private Set<IcfgLocation> mErrorLocations;
	private ExecutionTermintionReason aggregateOutputType;
	private int aggregateOutputCount;
	private boolean mIsAggregateFull;
	private static IcfgInterpreterObserver mInstance = null;

	public IcfgInterpreterObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mInstance = this;
	}

	public static ILogger getLogger() {
		return mInstance == null ? null : mInstance.mLogger;
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (root instanceof final IIcfg<?> icfg) {
			if (mIcfg != null) {
				throw new UnsupportedOperationException("Multiple CFGs are not supported.");
			}
			// TODO: Extract executions from mIcfg (mServices will be also needed for some operations)
			// This should be probably moved to a separate class

			// Useful methods:
			// * mIcfg.getCfgSmtToolkit().getManagedScript()
			// (also .getScript() if the Script instead of the ManagedScript is needed)
			// * mIcfg.getInitialNodes()
			// * TransFormulaUtils.computeGuard
			// * SmtUtils.getConjuncts
			// * SmtUtils.toDnf
			// * mLogger can be used for output (e.g., for debugging)
			try {
				// initiate / reset all variables
				mIcfg = icfg;
				mErrorLocations = Set.copyOf(IcfgUtils.getErrorLocations(mIcfg));
				mExecutions = new HashMap<>();
				mFinalResults = new HashMap<>();
				mIsAggregateFull = false;
				mAggregateExecutions = new ArrayList<>();

				IcfgInterpreterPreferences.updatePreferences();
				final ExecutionProducer producer = new ExecutionProducer(icfg, mServices, mErrorLocations);

				outputMethod = IcfgInterpreterPreferences.getPreferences().getEnum(
						IcfgInterpreterPreferences.SettingLabel.OUTPUT_METHOD.toString(),
						IcfgInterpreterPreferences.OutputMethod.class);

				aggregateOutputType = IcfgInterpreterPreferences.getPreferences().getEnum(
						IcfgInterpreterPreferences.SettingLabel.AGGREGATE_RESULTS_TYPE.toString(),
						ExecutionTermintionReason.class);
				aggregateOutputCount = IcfgInterpreterPreferences.getPreferences()
						.getInt(IcfgInterpreterPreferences.SettingLabel.AGGREGATE_RESULTS_NUMBER.toString());

				terminationCount = new HashMap<>();
				for (final ExecutionTermintionReason reason : ExecutionTermintionReason.values()) {
					terminationCount.put(reason, 0);
				}
				for (final IcfgLocation loc : mErrorLocations) {
					mFinalResults.put(loc, new UnprovableResult<>(Activator.PLUGIN_ID, loc,
							mServices.getBacktranslationService(), null, "No error execution found"));
				}
				final File tempDir;
				if (outputMethod.equals(OutputMethod.PRINT_TO_FILE)) {
					tempDir = Files.createTempDirectory("IcfgInterpreter_Results").toFile();
					outputDirs = new HashMap<>();
					for (final ExecutionTermintionReason reason : ExecutionTermintionReason.values()) {
						final File reasonDirectory = new File(tempDir, reason.toString());
						reasonDirectory.mkdirs();
						outputDirs.put(reason, reasonDirectory);
					}
				} else {
					tempDir = null;
				}

				// Create executions
				mExecutions = producer.makeExecutions(mLogger,
						(executions, locations) -> outputBatch(executions, locations));

				// Either no execution of the target type was found, or mExecutions is empty because of batching and
				// should be supplemented with the batch aggregate.
				if (!mExecutions.containsKey(aggregateOutputType) || mExecutions.get(aggregateOutputType).isEmpty()) {
					mExecutions.put(aggregateOutputType, mAggregateExecutions);
				}

				// Report results of batches
				for (final IcfgLocation loc : mErrorLocations) {
					mServices.getResultService().reportResult(Activator.PLUGIN_ID, mFinalResults.get(loc));
				}

				final int total = terminationCount.values().stream().reduce(0, (i, j) -> i + j);

				mLogger.info("Produced %s program executions", total);
				for (final Entry<ExecutionTermintionReason, Integer> entry : terminationCount.entrySet()) {
					mLogger.info("%s executions: %s", entry.getKey().name(), entry.getValue());
				}
				if (outputMethod.equals(OutputMethod.PRINT_TO_FILE)) {
					mLogger.info("Stored on path " + tempDir.getAbsolutePath());
				}

			} catch (final Exception e) {
				final ByteArrayOutputStream bs = new ByteArrayOutputStream();
				final PrintStream message = new PrintStream(bs);
				e.printStackTrace(message);
				mLogger.error(bs.toString(StandardCharsets.UTF_8));
			}
		}
		return false;
	}

	public boolean isAggregateFull() {
		return mIsAggregateFull;
	}

	private void outputBatch(final Map<ExecutionTermintionReason, List<PartialExecution>> executions,
			final Set<IcfgLocation> errorLocations) {

		final Map<IcfgLocation, PartialExecution> locs2ErrorExecutions = executions
				.getOrDefault(ExecutionTermintionReason.REACHED_ERROR, List.of()).stream()
				.collect(Collectors.toMap(x -> x.currentLocation(), x -> x, (x, y) -> x));

		for (final IcfgLocation loc : errorLocations) {
			final PartialExecution errorExecution = locs2ErrorExecutions.get(loc);

			if (errorExecution != null && mFinalResults.get(loc) instanceof UnprovableResult) {
				// We have a counter example, and there is no previous counter example for this location.
				final IResult result = new CounterExampleResult<>(loc, Activator.PLUGIN_ID,
						mServices.getBacktranslationService(), ProgramExecutions.translateExecution(errorExecution,
								mIcfg.getCfgSmtToolkit().getManagedScript()));
				mFinalResults.put(loc, result);
			}
		}

		int newTotalExecutions = 0;
		switch (outputMethod) {
		case DONT_PRINT:
			for (final Entry<ExecutionTermintionReason, List<PartialExecution>> entry : executions.entrySet()) {
				final ExecutionTermintionReason reason = entry.getKey();
				addBatchToAggregateResult(reason, entry.getValue());
				final int newExecutions = entry.getValue().size();
				terminationCount.put(reason, terminationCount.get(reason) + newExecutions);
				newTotalExecutions += newExecutions;
			}
			break;
		case PRINT_TO_FILE:
			final String nameBase = "Execution_" + String.valueOf(System.currentTimeMillis()) + "_";
			for (final Entry<ExecutionTermintionReason, List<PartialExecution>> entry : executions.entrySet()) {
				final ExecutionTermintionReason reason = entry.getKey();
				addBatchToAggregateResult(reason, entry.getValue());
				final File directory = outputDirs.get(reason);
				final int newExecutions = entry.getValue().size();
				terminationCount.put(reason, terminationCount.get(reason) + newExecutions);
				newTotalExecutions += newExecutions;

				int i = 0;
				for (final var e : entry.getValue()) {
					final File outputFile = new File(directory, nameBase + String.valueOf(i) + ".txt");
					i++;
					try {
						outputFile.createNewFile();
						final BufferedWriter out = new BufferedWriter(
								new OutputStreamWriter(new FileOutputStream(outputFile)));

						// final String executionSimplified = mServices.getBacktranslationService()
						// .translateProgramExecution(e).toString();
						out.write("Ended because of " + reason + "\n" + e /* + "\n" + executionSimplified */);
						out.close();
					} catch (final IOException e1) {
						e1.printStackTrace();
					}
				}
			}
			break;
		case PRINT_TO_TERMINAL:
			for (final Entry<ExecutionTermintionReason, List<PartialExecution>> entry : executions.entrySet()) {
				final ExecutionTermintionReason reason = entry.getKey();
				addBatchToAggregateResult(reason, entry.getValue());

				final int newExecutions = entry.getValue().size();
				terminationCount.put(reason, terminationCount.get(reason) + newExecutions);
				newTotalExecutions += newExecutions;

				for (final var e : entry.getValue()) {

					// final String executionSimplified = mServices.getBacktranslationService()
					// .translateProgramExecution(e).toString();

					mLogger.info("Ended because of %s\n\n%s\n\n%s", reason, e/* , executionSimplified */);
				}
			}
			break;
		default:
			break;
		}

		mLogger.info("Processed batch of %s executions", newTotalExecutions);
	}

	private void addBatchToAggregateResult(final ExecutionTermintionReason reason,
			final List<PartialExecution> executions) {
		if (aggregateOutputType != reason || mIsAggregateFull) {
			return;
		}

		int size = mAggregateExecutions.size();
		for (final PartialExecution execution : executions) {
			if (size >= aggregateOutputCount) {
				break;
			}
			mAggregateExecutions.add(execution);
			size++;
		}
		// We do not set this on the break condition because the loop may end exactly when the aggregate becomes full.
		if (size == aggregateOutputCount) {
			mIsAggregateFull = true;
		}
	}

	public static IcfgInterpreterObserver getInstance() {
		return mInstance;
	}

	public IElement getExecutions() {
		return new ProgramExecutions(new HashMap<>(mExecutions));
	}
}
