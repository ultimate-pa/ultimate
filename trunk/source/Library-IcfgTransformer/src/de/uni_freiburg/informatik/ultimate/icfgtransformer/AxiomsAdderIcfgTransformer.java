package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.IdentityTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtSymbols;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Alexander Nutz
 *
 */
public class AxiomsAdderIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final BasicIcfg<OUTLOC> mResult;

	public AxiomsAdderIcfgTransformer(final ILogger logger, final String resultName, final Class<OUTLOC> outLocClazz,
			final IIcfg<INLOC> inputCfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final Term additionalAxioms) {
		assert logger != null;

		final CfgSmtToolkit inputCfgCsToolkit = inputCfg.getCfgSmtToolkit();
		final ManagedScript mgdScript = inputCfgCsToolkit.getManagedScript();

		final SmtSymbols newSmtSymbols =
				inputCfgCsToolkit.getSmtSymbols().addAxiom(mgdScript.getScript(), additionalAxioms);

		final CfgSmtToolkit newToolkit = new CfgSmtToolkit(inputCfgCsToolkit.getModifiableGlobalsTable(), mgdScript,
				inputCfgCsToolkit.getSymbolTable(), inputCfgCsToolkit.getProcedures(), inputCfgCsToolkit.getInParams(),
				inputCfgCsToolkit.getOutParams(), inputCfgCsToolkit.getIcfgEdgeFactory(),
				inputCfgCsToolkit.getConcurrencyInformation(), newSmtSymbols);

		// make a copy of the input Icfg
		// TODO: Seems really expensive
		final ITransformulaTransformer noopTransformulaTransformer = new IdentityTransformer(inputCfgCsToolkit);
		final IcfgTransformer<INLOC, OUTLOC> noopIcfgTransformer = new IcfgTransformer<>(logger, inputCfg, funLocFac,
				backtranslationTracker, outLocClazz, resultName, noopTransformulaTransformer);
		final BasicIcfg<OUTLOC> copiedIcfg = (BasicIcfg<OUTLOC>) noopIcfgTransformer.getResult();
		copiedIcfg.setCfgSmtToolkit(newToolkit);

		mResult = copiedIcfg;
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResult;
	}

}
