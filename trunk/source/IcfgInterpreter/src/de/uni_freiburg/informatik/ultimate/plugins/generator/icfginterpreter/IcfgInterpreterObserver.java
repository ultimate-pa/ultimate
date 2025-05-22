package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.Random;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ExecutionProducer.LessCodeExecutionProducer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramExecutions.ExecutionTermintionReason;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramExecutions.Pair;

public class IcfgInterpreterObserver extends BaseObserver {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private IIcfg<? extends IcfgLocation> mIcfg;
	private List<Pair<IcfgProgramExecution<IcfgEdge>, ExecutionTermintionReason>> mExecutions = List.of();
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
				final Random random = new Random();
				final long seed = random.nextLong();
				mExecutions = ExecutionProducer.makeExecutions(mIcfg, mServices, mLogger,
						new LessCodeExecutionProducer(), new Random(seed));
				ExecutionProducer.makeExecutions(mIcfg, mServices, mLogger, new LessCodeExecutionProducer(),
						new Random(seed));
			} catch (final Exception e) {
				final ByteArrayOutputStream bs = new ByteArrayOutputStream();
				final PrintStream message = new PrintStream(bs);
				e.printStackTrace(message);
				mLogger.error(bs.toString(StandardCharsets.UTF_8));
			}
		}
		// TODO: We should probably not output all executions
		// TODO: Improve format
		mLogger.info("Produced %s program executions", mExecutions.size());
		for (final var e : mExecutions) {
			mLogger.info("Ended because of %s\n\n%s", e.b(), e.a());
		}
		return false;
	}

	public static IcfgInterpreterObserver getInstance() {
		return mInstance;
	}

	public IElement getExecutions() {
		return new ProgramExecutions<>(List.copyOf(mExecutions));
	}
}
