/*
 * Copyright (C) 2017 Moritz Mohr (mohrm@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.mohr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.IdentityTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class IcfgLoopTransformerMohr<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final IIcfg<OUTLOC> mResult;
	private final TransformedIcfgBuilder<INLOC, OUTLOC> mTib;
	private final ManagedScript mManagedScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final Map<INLOC, Boolean> mOverApproximation;

	public IcfgLoopTransformerMohr(final ILogger logger, final IUltimateServiceProvider services,
			final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final Class<OUTLOC> outLocationClass,
			final String newIcfgIdentifier) {

		// Notes:
		// new Overapprox("Because of loop acceleration", null).annotate(edge)

		mOverApproximation = new HashMap<>();

		mManagedScript = originalIcfg.getCfgSmtToolkit().getManagedScript();
		mServices = services;
		mLogger = logger;
		mSymbolTable = originalIcfg.getCfgSmtToolkit().getSymbolTable();
		final BasicIcfg<OUTLOC> resultIcfg =
				new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
		final IdentityTransformer identityTransformer = new IdentityTransformer(originalIcfg.getCfgSmtToolkit());
		mTib = new TransformedIcfgBuilder<>(mLogger, funLocFac, backtranslationTracker, identityTransformer,
				originalIcfg, resultIcfg);

		transform(originalIcfg);
		mTib.finish();
		mResult = resultIcfg;

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(mResult);
		}

	}

	@SuppressWarnings("unchecked")
	private void transform(final IIcfg<INLOC> origIcfg) {
		final IcfgLoopDetection<INLOC> loopDetector = new IcfgLoopDetection<>(mLogger, mServices, origIcfg);
		final Set<IcfgLoop<INLOC>> loops = loopDetector.getResult();
		final Set<INLOC> loopHeads = new HashSet<>();
		final Set<INLOC> loopNodes = new HashSet<>();
		final Map<INLOC, UnmodifiableTransFormula> loopSummaries = new HashMap<>();
		final Map<INLOC, Set<Pair<UnmodifiableTransFormula, INLOC>>> loopExits = new HashMap<>();
		if (!loops.isEmpty()) {
			for (final IcfgLoop<INLOC> loop : loops) {
				loopHeads.add(loop.getHead());
				loopNodes.addAll(loop.getLoopbody());
				loopSummaries.put(loop.getHead(), transformLoop(loop));
				loopExits.put(loop.getHead(), new HashSet<>());
				for (final Pair<List<UnmodifiableTransFormula>, INLOC> exitPath : loop.getLoopExits()) {
					final UnmodifiableTransFormula exitUtf =
							TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript, false, false,
									false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
									SimplificationTechnique.SIMPLIFY_DDA, exitPath.getFirst());
					mLogger.info("Found exit path: " + exitUtf);
					loopExits.get(loop.getHead()).add(new Pair<>(exitUtf, exitPath.getSecond()));
				}
			}
		}

		// build new IIcfg
		final ArrayDeque<INLOC> queue = new ArrayDeque<>();
		final Set<INLOC> visited = new HashSet<>();
		queue.add(origIcfg.getInitialNodes().iterator().next());

		final List<Triple<OUTLOC, OUTLOC, IcfgEdge>> rtrTransitions = new ArrayList<>();

		while (!queue.isEmpty()) {
			final INLOC node = queue.removeFirst();
			visited.add(node);
			final OUTLOC newSource = mTib.createNewLocation(node);
			for (final IcfgEdge edge : node.getOutgoingEdges()) {
				if (loopNodes.contains(edge.getTarget()) && !loopHeads.contains(edge.getTarget())
						|| node.equals(edge.getTarget())) {
					continue;
				} else if (!visited.contains(edge.getTarget())) {
					queue.add((INLOC) edge.getTarget());
				}
				final OUTLOC newTarget = mTib.createNewLocation((INLOC) edge.getTarget());
				if (loopHeads.contains(node)) {
					final UnmodifiableTransFormula loopSummary = loopSummaries.get(node);
					final UnmodifiableTransFormula utf = TransFormulaUtils.sequentialComposition(mLogger, mServices,
							mManagedScript, false, false, false,
							XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
							SimplificationTechnique.SIMPLIFY_DDA, Arrays.asList(loopSummary, edge.getTransformula()));
					mLogger.info("Loop Summary Transformula: " + utf);
					final IcfgEdge e =
							mTib.createNewInternalTransition(newSource, newTarget, utf, mOverApproximation.get(node));
					new Overapprox("Because of loop acceleration", null).annotate(e);
					for (final Pair<UnmodifiableTransFormula, INLOC> exit : loopExits.get(node)) {
						final OUTLOC exitTarget = mTib.createNewLocation(exit.getSecond());
						final UnmodifiableTransFormula exitSummary = TransFormulaUtils.sequentialComposition(mLogger,
								mServices, mManagedScript, false, false, false,
								XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
								SimplificationTechnique.SIMPLIFY_DDA, Arrays.asList(loopSummary, exit.getFirst()));
						final IcfgEdge o = mTib.createNewInternalTransition(newSource, exitTarget, exitSummary,
								mOverApproximation.get(node));
						new Overapprox("Because of loop acceleration", null).annotate(o);
					}

				} else {
					if (edge instanceof IIcfgReturnTransition<?, ?>) {
						mLogger.info("Return: " + newSource + " - " + edge + " -> " + newTarget);
						rtrTransitions.add(new Triple<OUTLOC, OUTLOC, IcfgEdge>(newSource, newTarget, edge));
					} else {
						if (edge instanceof IIcfgCallTransition<?>) {
							mLogger.info("Call: " + newSource + " - " + edge + " -> " + newTarget);
						}
						mLogger.info("Internal: " + newSource + " - " + edge + " -> " + newTarget);
						mTib.createNewTransition(newSource, newTarget, edge);
					}
				}
			}
		}

		rtrTransitions.forEach(a -> mTib.createNewTransition(a.getFirst(), a.getSecond(), a.getThird()));

	}

	@SuppressWarnings("unchecked")
	private UnmodifiableTransFormula transformLoop(final IcfgLoop<INLOC> loop) {
		final List<Map<IProgramVar, Term>> pathSymbolicMemory = new ArrayList<>();
		final List<UnmodifiableTransFormula> pathGuards = new ArrayList<>();
		final SymbolicMemory symbolicMemory = new SymbolicMemory(mManagedScript, mLogger);
		int pathCount = 0;

		final ArrayDeque<TransFormula> queue = new ArrayDeque<>();

		for (final ArrayList<IcfgEdge> path : loop.getPaths()) {
			final List<UnmodifiableTransFormula> formulas = new ArrayList<>();
			for (final IcfgEdge edge : path) {
				if (loop.getNestedLoopHeads().contains(edge.getSource())) {
					// compute summary of nested loop and add them to the path
					formulas.add(transformLoop(loop.getNestedLoop((INLOC) edge.getSource())));
					mLogger.debug("nested Loop @" + edge.getSource() + " : " + formulas.get(formulas.size() - 1));
				}
				formulas.add(edge.getTransformula());
			}

			final UnmodifiableTransFormula composition = TransFormulaUtils.sequentialComposition(mLogger, mServices,
					mManagedScript, false, false, false, null, SimplificationTechnique.NONE, formulas);

			mLogger.debug("Path formulas: " + formulas);
			mLogger.debug("Composition: " + composition);

			queue.addAll(getDisjunctsFromTransformula(composition));

		}

		while (!queue.isEmpty()) {

			final TransFormula path = queue.remove();
			symbolicMemory.newPath();

			pathSymbolicMemory.add(new HashMap<>());

			// DD: Note that the issue with the "IllegalArgumentException: cannot bring into simultaneous update form
			// xxx outvar occurs in several conjuncts" still persists. I have to check with Matthias if we can fix this.
			// Until then, you can just ignore these errors.

			final SimultaneousUpdate su = new SimultaneousUpdate(path, mManagedScript);
			final Map<IProgramVar, Term> varUpdates = su.getUpdatedVars();
			final Set<IProgramVar> havocVars = su.getHavocedVars();
			mLogger.debug("Updates: " + varUpdates + " havocs: " + havocVars);
			if (!havocVars.isEmpty()) {
				mOverApproximation.put(loop.getHead(), true);
			}
			pathGuards.add(TransFormulaUtils.computeGuard((UnmodifiableTransFormula) path, mManagedScript, mServices, mLogger));

			// calculate symbolic memory of the path
			for (final Map.Entry<IProgramVar, Term> newValue : varUpdates.entrySet()) {
				if (newValue.getValue() instanceof ConstantTerm || newValue.getValue() instanceof TermVariable) {
					symbolicMemory.updateConst(newValue.getKey(), newValue.getValue(), mSymbolTable);
				} else if (newValue.getValue() instanceof ApplicationTerm
						&& ("+".equals(((ApplicationTerm) newValue.getValue()).getFunction().getName())
								|| "-".equals(((ApplicationTerm) newValue.getValue()).getFunction().getName()))) {
					final Set<TermVariable> freeVars =
							new HashSet<>(Arrays.asList(newValue.getValue().getFreeVars()));
					if (freeVars.contains(newValue.getKey().getTermVariable())) {
						symbolicMemory.updateInc(newValue.getKey(), newValue.getValue(), mSymbolTable);
					} else {
						symbolicMemory.updateConst(newValue.getKey(), newValue.getValue(), mSymbolTable);
					}
				} else {
					symbolicMemory.updateUndefined(newValue.getKey(), mSymbolTable);
				}
			}
			pathCount++;
		}

		final List<Term> pathTerms = new ArrayList<>();
		for (int i = 0; i < pathCount; i++) {
			pathTerms.add(symbolicMemory.getFormula(i, pathGuards.get(i)));
		}
		final Term varUpdate = symbolicMemory.getVarUpdateTerm();
		if (varUpdate != null) {
			pathTerms.add(varUpdate);
		}
		pathTerms.add(symbolicMemory.getKappaMin());
		final Term loopSummary =
				SmtUtils.and(mManagedScript.getScript(), pathTerms.toArray(new Term[pathTerms.size()]));

		final Map<IProgramVar, TermVariable> inVars = symbolicMemory.getInVars();
		final Map<IProgramVar, TermVariable> outVars = symbolicMemory.getOutVars();

		final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, outVars, true, null, true, null, false);
		final Set<TermVariable> aux = symbolicMemory.getKappas();
		aux.addAll(symbolicMemory.getTaus());
		final Term quantFreeFormula = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mManagedScript,
				loopSummary, SimplificationTechnique.SIMPLIFY_DDA,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		tfb.setFormula(quantFreeFormula);
		tfb.addAuxVarsButRenameToFreshCopies(aux, mManagedScript);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);

		if (symbolicMemory.containsUndefined()) {
			mOverApproximation.put(loop.getHead(), true);
		} else {
			mOverApproximation.put(loop.getHead(), false);
		}

		return tfb.finishConstruction(mManagedScript);
	}

	/**
	 * Converts a given transformula to DNF and returns a list of transformulas for each disjunct.
	 */
	private List<TransFormula> getDisjunctsFromTransformula(final TransFormula originalTf) {
		final Term dnf = SmtUtils.toDnf(mServices, mManagedScript, originalTf.getFormula(),
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("DNF: " + dnf.toStringDirect());
		}
		final Term[] disjuncts = SmtUtils.getDisjuncts(dnf);
		if (disjuncts.length == 1) {
			return Collections.singletonList(originalTf);
		}
		final List<TransFormula> rtr = new ArrayList<>(disjuncts.length);
		final Map<IProgramVar, TermVariable> inVars = originalTf.getInVars();
		final Map<IProgramVar, TermVariable> outVars = originalTf.getOutVars();
		final Set<IProgramConst> nonTheoryConsts = originalTf.getNonTheoryConsts();
		final Collection<TermVariable> branchEncoders = Collections.emptySet();
		final boolean emptyAuxVars = originalTf.getAuxVars().isEmpty();
		for (final Term disjunct : disjuncts) {
			final Term simpl =
					SmtUtils.simplify(mManagedScript, disjunct, mServices, SimplificationTechnique.SIMPLIFY_DDA);
			final TransFormulaBuilder tfBuilder = new TransFormulaBuilder(inVars, outVars, nonTheoryConsts.isEmpty(),
					nonTheoryConsts, branchEncoders.isEmpty(), branchEncoders, emptyAuxVars);
			tfBuilder.setFormula(simpl);
			tfBuilder.setInfeasibility(Infeasibility.NOT_DETERMINED);
			final UnmodifiableTransFormula disjunctTf = tfBuilder.finishConstruction(mManagedScript);
			rtr.add(disjunctTf);
		}
		return rtr;
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResult;
	}

}
