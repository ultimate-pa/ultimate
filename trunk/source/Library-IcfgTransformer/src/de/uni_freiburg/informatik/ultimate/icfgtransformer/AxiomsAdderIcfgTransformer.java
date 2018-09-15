package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.IdentityTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class AxiomsAdderIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
	implements IIcfgTransformer<OUTLOC> {

	private final BasicIcfg<OUTLOC> mResult;

	public AxiomsAdderIcfgTransformer(final ILogger logger, final String resultName,
			final Class<OUTLOC> outLocClazz, final IIcfg<INLOC> inputCfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker,
			final Term additionalAxioms) {
//			final Collection<Term> locationLiterals) {
//			final Set<IProgramConst> locationLiterals) {
		assert logger != null;

		final CfgSmtToolkit inputCfgCsToolkit = inputCfg.getCfgSmtToolkit();
//
		final ManagedScript mgdScript = inputCfgCsToolkit.getManagedScript();

		assert inputCfgCsToolkit.getAxioms().getClosedFormula() == inputCfgCsToolkit.getAxioms().getFormula();
		final Term newAxioms = SmtUtils.and(mgdScript.getScript(), inputCfgCsToolkit.getAxioms().getClosedFormula(),
				additionalAxioms);

		assert additionalAxioms.getFreeVars().length == 0 : "axioms must be closed";

		final IPredicate newAxiomsPred = new BasicPredicate(Boogie2SMT.HARDCODED_SERIALNUMBER_FOR_AXIOMS, new String[0],
				additionalAxioms, Collections.emptySet(), newAxioms);


		final CfgSmtToolkit newToolkit = new CfgSmtToolkit(inputCfgCsToolkit.getModifiableGlobalsTable(), mgdScript,
				inputCfgCsToolkit.getSymbolTable(), newAxiomsPred, inputCfgCsToolkit.getProcedures(),
				inputCfgCsToolkit.getInParams(), inputCfgCsToolkit.getOutParams(),
				inputCfgCsToolkit.getIcfgEdgeFactory(), inputCfgCsToolkit.getConcurrencyInformation());

		// make a copy of the input Icfg
		final ITransformulaTransformer noopTransformulaTransformer =
				new IdentityTransformer(inputCfgCsToolkit);
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
