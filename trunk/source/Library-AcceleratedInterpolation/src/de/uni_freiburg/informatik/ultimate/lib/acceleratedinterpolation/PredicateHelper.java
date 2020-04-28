package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class PredicateHelper<LETTER extends IIcfgTransition<?>> {
	private final IPredicateUnifier mPredicateUnifier;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredTransformer;
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;

	public PredicateHelper(final IPredicateUnifier predicateUnifier,
			final PredicateTransformer<Term, IPredicate, TransFormula> predTransformer, final ILogger logger,
			final ManagedScript script, final IUltimateServiceProvider services) {
		mPredicateUnifier = predicateUnifier;
		mPredTransformer = predTransformer;
		mScript = script;
		mLogger = logger;
		mServices = services;
	}

	public UnmodifiableTransFormula traceToTf(final List<LETTER> trace) {
		final List<UnmodifiableTransFormula> tfs = new ArrayList<>();
		for (final LETTER l : trace) {
			tfs.add(l.getTransformula());
		}
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mScript, true, true, true,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, SimplificationTechnique.SIMPLIFY_DDA, tfs);
	}

	public List<UnmodifiableTransFormula> traceToListOfTfs(final List<LETTER> trace) {
		final List<UnmodifiableTransFormula> tfs = new ArrayList<>();
		for (final LETTER l : trace) {
			tfs.add(l.getTransformula());
		}
		return tfs;
	}
}
