package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramExecutions.ExecutionTermintionReason;

public class IcfgInterpreterObserver extends BaseObserver {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private IIcfg<? extends IcfgLocation> mIcfg;
	private Map<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>> mExecutions = new HashMap<>();
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
			mIcfg = icfg;
			mExecutions = new HashMap<>();
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
				final ExecutionProducer producer = new ExecutionProducer(icfg, mServices);
				mExecutions = producer.makeExecutions(mLogger);
			} catch (final Exception e) {
				final ByteArrayOutputStream bs = new ByteArrayOutputStream();
				final PrintStream message = new PrintStream(bs);
				e.printStackTrace(message);
				mLogger.error(bs.toString(StandardCharsets.UTF_8));
			}
		}
		if (mIcfg != null) {
			// TODO: We should probably not output all executions
			// TODO: Improve format
			int total = 0;
			for (final Entry<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>> entry : mExecutions
					.entrySet()) {
				final ExecutionTermintionReason reason = entry.getKey();
				total += entry.getValue().size();
				for (final var e : entry.getValue()) {
					mLogger.info("Ended because of %s\n\n%s", reason, e);
				}
			}
			mLogger.info("Produced %s program executions", total);

			// TODO: Add a setting for this or move it to another plugin
			reportSafetyResults();
		}
		return false;
	}

	private void reportSafetyResults() {
		final Map<IcfgLocation, IcfgProgramExecution<IcfgEdge>> locs2ErrorExecutions = mExecutions
				.getOrDefault(ExecutionTermintionReason.REACHED_ERROR, new ArrayList<>()).stream().collect(Collectors
						.toMap(x -> x.getTraceElement(x.getLength() - 1).getStep().getTarget(), x -> x, (x, y) -> x));

		for (final IcfgLocation loc : IcfgUtils.getErrorLocations(mIcfg)) {
			final IcfgProgramExecution<IcfgEdge> errorExecution = locs2ErrorExecutions.get(loc);
			final IResult result;
			if (errorExecution == null) {
				result = new UnprovableResult<>(Activator.PLUGIN_ID, loc, mServices.getBacktranslationService(), null,
						"No error execution found");
			} else {
				result = new CounterExampleResult<>(loc, Activator.PLUGIN_ID, mServices.getBacktranslationService(),
						errorExecution);
			}
			mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		}
	}

	public static IcfgInterpreterObserver getInstance() {
		return mInstance;
	}

	public IElement getExecutions() {
		return new ProgramExecutions<>(new HashMap<>(mExecutions));
	}
}
