package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Random;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IcfgExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IcfgTranslation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.Settings;

public class IcfgInterpreterObserver extends BaseObserver {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private IIcfg<? extends IcfgLocation> mIcfg;
	private HashMap<IcfgLocation, ArrayList<ICFGExecutionEdge>> sourceToEdge;

	public IcfgInterpreterObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (root instanceof final IIcfg<?> icfg) {
			if (mIcfg != null) {
				throw new UnsupportedOperationException("Multiple CFGs are not supported.");
			}
			mIcfg = icfg;
		}
		return false;
	}

	@Override
	public void finish() {
		if (mIcfg == null) {
			return;
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
		final int testExecutionCount = 5;
		sourceToEdge = IcfgTranslation.edgeBFS(mIcfg, mServices);
		final Set<? extends IcfgLocation> initialNodes = mIcfg.getInitialNodes();
		final NonDeterministicChoice ndc = Settings.getSettings().getNDC();
		final Random random = new Random();
		for (final IcfgLocation node : initialNodes) {
			for (final ICFGExecutionEdge outEdge : sourceToEdge.get(node)) {
				for (int i = 0; i < testExecutionCount; i++) {
					final long seed = random.nextLong();

					final NonDeterministicChoice ndcInstance = ndc.newInstance(seed);
					final ProgramState state = new ProgramState(outEdge.getVariables(), ndcInstance);
					final IcfgExecution execution = new IcfgExecution(state, node);

					final ArrayList<ICFGExecutionEdge> nextEdges = new ArrayList<>();
					nextEdges.add(outEdge);

					while (!nextEdges.isEmpty()) {
						final ArrayList<ICFGExecutionEdge> availableEdges = Util.filter(nextEdges, (edge) -> {
							return edge.canBeTaken(state);
						});

						ICFGExecutionEdge nextEdge;
						if (availableEdges.size() > 1) {
							nextEdge = ndcInstance.chooseEdge(availableEdges);
						} else if (availableEdges.size() == 0) {
							// No guard was true, or no edges exist from the current vertex
							break;
						} else {
							nextEdge = availableEdges.get(0);
						}

						nextEdge.execute(state, ndcInstance);
						execution.addStep(state, nextEdge.mTarget);
						nextEdges.clear();
						nextEdges.addAll(sourceToEdge.getOrDefault(nextEdge.mTarget, new ArrayList<>()));
					}
					System.out.println("Execution " + (i + 1) + "\n" + execution + "\n");
					nextEdges.clear();
				}

			}
		}
	}

	public IElement getRootOfNewModel() {
		// TODO: We want to return executions instead (for now we can also just log them, but e.g., to give the
		// execution to other plugins)
		return mIcfg;
	}
}
