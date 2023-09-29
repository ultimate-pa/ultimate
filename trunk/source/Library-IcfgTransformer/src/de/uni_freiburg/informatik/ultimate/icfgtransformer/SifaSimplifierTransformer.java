package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.sifa.SifaBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.sifa.SifaBuilder.SifaComponents;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class SifaSimplifierTransformer implements ITransformulaTransformer {
	// TODO: What is a reasonable timeout? And what to do if we exceed it?
	private static final long SIFA_TIMEOUT = 5 * 1000;
	private static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA;

	private final IUltimateServiceProvider mServices;
	private Map<IcfgLocation, IPredicate> mSifaPredicates;
	private final CfgSmtToolkit mToolkit;

	public SifaSimplifierTransformer(final IUltimateServiceProvider services, final CfgSmtToolkit toolkit) {
		mServices = services;
		mToolkit = toolkit;
	}

	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		final ILogger logger = mServices.getLoggingService().getLogger(getClass());
		// TODO: Can we reduce this number of locations?
		final Set<IcfgLocation> locations =
				icfg.getProgramPoints().values().stream().flatMap(x -> x.values().stream()).collect(Collectors.toSet());
		final SifaComponents sifa = new SifaBuilder(mServices, logger).construct((IIcfg<IcfgLocation>) icfg,
				mServices.getProgressMonitorService().getChildTimer(SIFA_TIMEOUT), locations);
		mSifaPredicates = sifa.getIcfgInterpreter().interpret();
	}

	@Override
	public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula tf) {
		final IPredicate invariant = mSifaPredicates.get(oldEdge.getSource());
		if (invariant == null) {
			return new TransformulaTransformationResult(tf);
		}
		final Map<Term, Term> substitution = tf.getInVars().entrySet().stream()
				.collect(Collectors.toMap(x -> x.getKey().getTerm(), x -> x.getValue()));
		final ManagedScript managedScript = mToolkit.getManagedScript();
		final Term context = Substitution.apply(managedScript, substitution, invariant.getFormula());
		final Term newTerm =
				SmtUtils.simplify(managedScript, tf.getFormula(), context, mServices, SIMPLIFICATION_TECHNIQUE);
		final TransFormulaBuilder builder = new TransFormulaBuilder(tf.getInVars(), tf.getOutVars(), false,
				tf.getNonTheoryConsts(), false, tf.getBranchEncoders(), false);
		builder.setFormula(newTerm);
		if (SmtUtils.isFalseLiteral(newTerm)) {
			builder.setInfeasibility(Infeasibility.INFEASIBLE);
		} else {
			builder.setInfeasibility(tf.isInfeasible());
		}
		return new TransformulaTransformationResult(builder.finishConstruction(managedScript));
	}

	public Term backtranslate(final Term term) {
		// TODO: Implement
		return term;
	}

	@Override
	public String getName() {
		return getClass().getSimpleName();
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mToolkit.getSymbolTable();
	}

	@Override
	public HashRelation<String, IProgramNonOldVar> getNewModifiedGlobals() {
		return mToolkit.getModifiableGlobalsTable().getProcToGlobals();
	}

}
