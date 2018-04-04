package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class LoopInsertion<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> {

	private final ILogger mLogger;
	private final IIcfg<INLOC> mOriginalIcfg;
	private final Class<OUTLOC> mOutLocationClass;
	private final ILocationFactory<INLOC, OUTLOC> mFunLocFac;
	private final String mNewIcfgIdentifier;
	private final ITransformulaTransformer mTransformer;
	private final IBacktranslationTracker mBacktranslationTracker;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgScript;
	private final Script mScript;

	public LoopInsertion(final ILogger logger, final IIcfg<INLOC> originalIcfg, final Class<OUTLOC> outLocationClass,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final String newIcfgIdentifier,
			final ITransformulaTransformer transformer, final IBacktranslationTracker backtranslationTracker,
			final IUltimateServiceProvider services) {

		// Setup
		mLogger = logger;
		mOriginalIcfg = originalIcfg;
		mOutLocationClass = outLocationClass;
		mFunLocFac = funLocFac;
		mNewIcfgIdentifier = newIcfgIdentifier;
		mTransformer = transformer;
		mBacktranslationTracker = backtranslationTracker;
		mServices = services;
		final CfgSmtToolkit mCfgSmtToolkit = originalIcfg.getCfgSmtToolkit();
		mMgScript = mCfgSmtToolkit.getManagedScript();
		mScript = mMgScript.getScript();
	}

	public IIcfg<OUTLOC> rejoin2(final SimpleLoop originalLoop, final Term result, final Map<IProgramVar, Term> values,
			final TermVariable n) {

		final Script script = mMgScript.getScript();
		final Term zero = Rational.ZERO.toTerm(script.sort("Int"));
		final UnmodifiableTransFormula originalLoopTransFormula = originalLoop.mLoopTransFormula;
		final Map<Entry<UnmodifiableTransFormula, IcfgLocation>, UnmodifiableTransFormula> loopExits = new HashMap<>();
		final IcfgLocation loopHead = originalLoop.mHeadNode;

		for (final Entry<UnmodifiableTransFormula, IcfgLocation> exitEdge : originalLoop.mExitEdges) {
			// get LoopExit
			final UnmodifiableTransFormula exitTransformula = exitEdge.getKey();
			// joint the TransFormula
			Map<Term, Term> substitute = new HashMap<>();
			final Map<IProgramVar, TermVariable> outVars = new HashMap<>(exitTransformula.getOutVars());
			for (final IProgramVar var : originalLoopTransFormula.getOutVars().keySet()) {
				if (exitTransformula.getInVars().containsKey(var)) {
					substitute.put(exitTransformula.getInVars().get(var), values.get(var));
					if (exitTransformula.getInVars().get(var).equals(exitTransformula.getOutVars().get(var))) {
						outVars.remove(var);
						outVars.put(var, originalLoopTransFormula.getOutVars().get(var));
					}
				} else {
					outVars.put(var, originalLoopTransFormula.getOutVars().get(var));
				}
			}

			Substitution sub = new Substitution(mMgScript, substitute);
			final Term transformedExitFormula = sub.transform(exitTransformula.getFormula());

			// Quantifier - Start

			// replace n with j
			final TermVariable j = script.variable("j", script.sort("Int"));
			final Map<Term, Term> substituteJ = new HashMap<>();
			substituteJ.put(n, j);
			final Substitution subJ = new Substitution(mMgScript, substituteJ);
			final Term transformedExitFormulaJ = subJ.transform(transformedExitFormula);

			final Term conditions = script.term("xor", script.term(">=", j, n),
					script.term("or", script.term("<", j, zero), transformedExitFormulaJ));
			final Term quantifiedFormula = script.quantifier(Script.FORALL, new TermVariable[] { j }, conditions);

			final List<Term> remainingExitFormulas = new ArrayList<>();
			final TermVariable k = script.variable("k", script.sort("Int"));
			for (final Entry<UnmodifiableTransFormula, IcfgLocation> remainingExitEdge : originalLoop.mExitEdges) {
				final UnmodifiableTransFormula remainingExitTransformula = remainingExitEdge.getKey();
				// joint the TransFormula
				substitute = new HashMap<>();
				for (final IProgramVar var : originalLoopTransFormula.getOutVars().keySet()) {
					if (remainingExitTransformula.getInVars().containsKey(var)) {
						substitute.put(remainingExitTransformula.getInVars().get(var), values.get(var));
						if (remainingExitTransformula.getInVars().get(var)
								.equals(remainingExitTransformula.getOutVars().get(var))) {
							outVars.remove(var);
							outVars.put(var, originalLoopTransFormula.getOutVars().get(var));
						}
					} else {
						outVars.put(var, originalLoopTransFormula.getOutVars().get(var));
					}
				}

				sub = new Substitution(mMgScript, substitute);
				final Term remainingTransformedExitFormula = sub.transform(remainingExitTransformula.getFormula());

				// replace n with k
				final Map<Term, Term> substituteK = new HashMap<>();
				substituteK.put(n, k);
				final Substitution subK = new Substitution(mMgScript, substituteK);
				final Term transformedExitFormulaK = subK.transform(remainingTransformedExitFormula);
				remainingExitFormulas.add(transformedExitFormulaK);
			}
			Term quantifiedFormulaK = TransFormulaBuilder.getTrivialTransFormula(mMgScript).getFormula();
			if (remainingExitFormulas.size() > 1) {
				final Term additionalCondition =
						script.term("and", remainingExitFormulas.toArray(new Term[remainingExitFormulas.size()]));
				final Term conditionsK = script.term("xor", script.term(">=", k, n),
						script.term("or", script.term("<", k, zero), additionalCondition));
				quantifiedFormulaK = script.quantifier(Script.FORALL, new TermVariable[] { k }, conditionsK);
			}
			final Term jointTerm = script.quantifier(Script.EXISTS, new TermVariable[] { n },
					script.term("and", quantifiedFormula, quantifiedFormulaK, result));
			final Term simplified = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgScript,
					jointTerm, SimplificationTechnique.SIMPLIFY_DDA,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

			// Quantifier - End
			final TransFormulaBuilder tfb = new TransFormulaBuilder(originalLoopTransFormula.getInVars(), outVars,
					originalLoopTransFormula.getNonTheoryConsts().isEmpty(),
					originalLoopTransFormula.getNonTheoryConsts(),
					originalLoopTransFormula.getBranchEncoders().isEmpty(),
					originalLoopTransFormula.getBranchEncoders(), true);
			tfb.setFormula(simplified);
			tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
			tfb.finishConstruction(mMgScript);
			final UnmodifiableTransFormula loop = tfb.finishConstruction(mMgScript);
			loopExits.put(exitEdge, loop);
		}

		// create icfg
		mOriginalIcfg.getIdentifier();

		final BasicIcfg<OUTLOC> resultIcfg =
				new BasicIcfg<>(mNewIcfgIdentifier, mOriginalIcfg.getCfgSmtToolkit(), mOutLocationClass);
		final TransformedIcfgBuilder<INLOC, OUTLOC> lst = new TransformedIcfgBuilder<>(mLogger, mFunLocFac,
				mBacktranslationTracker, mTransformer, mOriginalIcfg, resultIcfg);
		processLocations(mOriginalIcfg.getInitialNodes(), lst, loopHead, loopExits);
		lst.finish();
		return resultIcfg;
	}

	public IIcfg<OUTLOC> rejoin(final SimpleLoop originalLoop, final Term result, final Map<IProgramVar, Term> values,
			final TermVariable n) {
		final Script script = mMgScript.getScript();
		final UnmodifiableTransFormula originalLoopTransFormula = originalLoop.mLoopTransFormula;
		final Map<Entry<UnmodifiableTransFormula, IcfgLocation>, UnmodifiableTransFormula> loopExits = new HashMap<>();
		final IcfgLocation loopHead = originalLoop.mHeadNode;

		for (final Entry<UnmodifiableTransFormula, IcfgLocation> exitEdge : originalLoop.mExitEdges) {
			// get LoopExit
			final UnmodifiableTransFormula exitTransformula = exitEdge.getKey();
			// joint the TransFormula
			final Map<Term, Term> substitute = new HashMap<>();
			final Map<IProgramVar, TermVariable> outVars = new HashMap<>(exitTransformula.getOutVars());
			for (final IProgramVar var : originalLoopTransFormula.getOutVars().keySet()) {
				if (exitTransformula.getInVars().containsKey(var)) {
					substitute.put(exitTransformula.getInVars().get(var), values.get(var));
					if (exitTransformula.getInVars().get(var).equals(exitTransformula.getOutVars().get(var))) {
						outVars.remove(var);
						outVars.put(var, originalLoopTransFormula.getOutVars().get(var));
					}
				} else {
					outVars.put(var, originalLoopTransFormula.getOutVars().get(var));
				}
			}

			final Substitution sub = new Substitution(mMgScript, substitute);
			final Term transformedExitFormula = script.term("not", sub.transform(exitTransformula.getFormula()));

			// Quantifier - Start

			// replace n with j
			final TermVariable j = script.variable("j", script.sort("Int"));
			final Map<Term, Term> substituteJ = new HashMap<>();
			substituteJ.put(n, j);
			final Substitution subJ = new Substitution(mMgScript, substituteJ);
			final Term transformedExitFormulaJ = subJ.transform(transformedExitFormula);

			final Term zero = Rational.ZERO.toTerm(script.sort("Int"));

			final Term conditions = script.term("xor", script.term(">=", j, n),
					script.term("or", script.term("<", j, zero), transformedExitFormulaJ));
			final Term quantifiedFormula = script.quantifier(Script.FORALL, new TermVariable[] { j }, conditions);
			final Term jointTerm = script.quantifier(Script.EXISTS, new TermVariable[] { n },
					script.term("and", quantifiedFormula, result));
			final Term simplified = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgScript,
					jointTerm, SimplificationTechnique.SIMPLIFY_DDA,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

			// Quantifier - End

			final TransFormulaBuilder tfb = new TransFormulaBuilder(originalLoopTransFormula.getInVars(), outVars,
					false, originalLoopTransFormula.getNonTheoryConsts(), true,
					originalLoopTransFormula.getBranchEncoders(), true);
			tfb.setFormula(simplified);
			tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
			tfb.finishConstruction(mMgScript);
			final UnmodifiableTransFormula loop = tfb.finishConstruction(mMgScript);
			loopExits.put(exitEdge, loop);
		}

		// create icfg
		mOriginalIcfg.getIdentifier();

		final BasicIcfg<OUTLOC> resultIcfg =
				new BasicIcfg<>(mNewIcfgIdentifier, mOriginalIcfg.getCfgSmtToolkit(), mOutLocationClass);
		final TransformedIcfgBuilder<INLOC, OUTLOC> lst = new TransformedIcfgBuilder<>(mLogger, mFunLocFac,
				mBacktranslationTracker, mTransformer, mOriginalIcfg, resultIcfg);
		processLocations(mOriginalIcfg.getInitialNodes(), lst, loopHead, loopExits);
		lst.finish();
		return resultIcfg;
	}

	private void processLocations(final Set<INLOC> init, final TransformedIcfgBuilder<INLOC, OUTLOC> lst,
			final IcfgLocation loopHead,
			final Map<Entry<UnmodifiableTransFormula, IcfgLocation>, UnmodifiableTransFormula> loopExits) {
		final Deque<INLOC> open = new ArrayDeque<>(init);
		final Set<INLOC> closed = new HashSet<>();

		while (!open.isEmpty()) {
			final INLOC oldSource = open.removeFirst();
			if (!closed.add(oldSource)) {
				continue;
			}
			if (oldSource.equals(loopHead)) {
				final OUTLOC newSource = lst.createNewLocation(oldSource);

				for (final Entry<UnmodifiableTransFormula, IcfgLocation> oldTransition : loopExits.keySet()) {
					final INLOC oldTarget = (INLOC) oldTransition.getValue();
					open.add(oldTarget);
					final OUTLOC newTarget = lst.createNewLocation(oldTarget);

					// TODO when is it an over-approximation
					final IcfgInternalTransition newTransition = lst.createNewInternalTransition(newSource, newTarget,
							loopExits.get(oldTransition), null, false);

					// new Overapprox("loop acceleration: ... ", null).annotate(newTransition);
					// mBacktranslationTracker.rememberRelation(oldTransition, newTransition);
				}
			} else {
				final OUTLOC newSource = lst.createNewLocation(oldSource);
				for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
					final INLOC oldTarget = (INLOC) oldTransition.getTarget();
					open.add(oldTarget);
					final OUTLOC newTarget = lst.createNewLocation(oldTarget);
					lst.createNewTransition(newSource, newTarget, oldTransition);
				}
			}
		}
	}

	private static IPayload getPayloadIfAvailable(final IElement elem) {
		if (elem == null) {
			return null;
		}
		if (elem.hasPayload()) {
			return elem.getPayload();
		}
		return null;
	}
}
