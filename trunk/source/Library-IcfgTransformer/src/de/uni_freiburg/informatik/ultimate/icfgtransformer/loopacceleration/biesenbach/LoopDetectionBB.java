/*
 * Copyright (C) 2017 Ben Biesenbach (Ben.Biesenbach@gmx.de)
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Extracts the loops from an {@link IIcfg}.
 *
 * @param <INLOC>
 *            The type of the locations of the IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the IIcfg with only loops left.
 *
 * @author Ben Biesenbach (Ben.Biesenbach@gmx.de)
 */
public class LoopDetectionBB<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> {

	private final ILogger mLogger;
	private final Deque<IIcfg<OUTLOC>> mLoopIcfgs = new ArrayDeque<>();
	private IUltimateServiceProvider mServices;
	private ManagedScript mMgScript;
	private INLOC mLoopHead;
	private IIcfg<INLOC> mOriginalIcfg;
	private ILocationFactory<INLOC, OUTLOC> mFunLocFac;
	private IBacktranslationTracker mBacktranslationTracker;
	private ITransformulaTransformer mTransformer;
	private String mNewIcfgIdentifier;
	private Class<OUTLOC> mOutLocationClass;

	/**
	 * Extracts the loops from an {@link IIcfg}.
	 *
	 * @param logger
	 * @param originalIcfg
	 * @param outLocationClass
	 * @param funLocFac
	 * @param newIcfgIdentifier
	 * @param transformer
	 * @param backtranslationTracker
	 * @param services
	 */
	@SuppressWarnings("unchecked")
	public LoopDetectionBB(final ILogger logger, final IIcfg<INLOC> originalIcfg, final Class<OUTLOC> outLocationClass,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final String newIcfgIdentifier,
			final ITransformulaTransformer transformer, final IBacktranslationTracker backtranslationTracker,
			final IUltimateServiceProvider services) {
		
		mServices = services;
		CfgSmtToolkit mCfgSmtToolkit = originalIcfg.getCfgSmtToolkit();
		mMgScript = mCfgSmtToolkit.getManagedScript();
		mFunLocFac = funLocFac;
		mBacktranslationTracker = backtranslationTracker;
		mTransformer = transformer;
		mNewIcfgIdentifier = newIcfgIdentifier;
		mOutLocationClass = outLocationClass;
		
		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mLogger = Objects.requireNonNull(logger);
		transformer.preprocessIcfg(origIcfg);
		mOriginalIcfg = origIcfg;

		for (final INLOC loopHead : origIcfg.getLoopLocations()) {
			// get path for every loop
			final Deque<INLOC> path = new ArrayDeque<>();
			path.addLast(loopHead);
			final Deque<INLOC> loopPath = getLoopPath(path);

			// set loopHead as initialNode
			final BasicIcfg<OUTLOC> initHelper =
					new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
			final TransformedIcfgBuilder<INLOC, OUTLOC> lstHelper =
					new TransformedIcfgBuilder<>(funLocFac, backtranslationTracker, transformer, origIcfg, initHelper);
			initHelper.addLocation((OUTLOC) loopPath.getFirst(), true, false, true, false, true);
			initHelper.addLocation((OUTLOC) origIcfg.getProcedureExitNodes().values().iterator().next(), false, false,
					false, true, false);
			lstHelper.finish();

			// get loop as Icfg
			final BasicIcfg<OUTLOC> resultLoop =
					new BasicIcfg<>(newIcfgIdentifier, initHelper.getCfgSmtToolkit(), outLocationClass);
			transformer.preprocessIcfg(initHelper);
			final TransformedIcfgBuilder<INLOC, OUTLOC> lst = new TransformedIcfgBuilder<>(funLocFac,
					backtranslationTracker, transformer, (IIcfg<INLOC>) initHelper, resultLoop);
			transformPathToIcfg((IIcfg<INLOC>) initHelper, loopPath, lst);
			lst.finish();

			mLoopIcfgs.addLast(resultLoop);
		}
		mLoopHead = origIcfg.getLoopLocations().iterator().next();
	}

	@SuppressWarnings("unchecked")
	private Deque<INLOC> getLoopPath(final Deque<INLOC> path) {
		Deque<INLOC> loopPath = null;
		for (final IcfgEdge transition : path.getLast().getOutgoingEdges()) {
			if (transition.getTarget().equals(path.getFirst())) {
				path.addLast((INLOC) transition.getTarget());
				return path;
			}
			final Deque<INLOC> newPath = new ArrayDeque<>(path);
			newPath.addLast((INLOC) transition.getTarget());
			final Deque<INLOC> returnedPath = getLoopPath(newPath);
			if (returnedPath != null) {
				loopPath = returnedPath;
			}
		}
		return loopPath;
	}

	@SuppressWarnings("unchecked")
	private void transformPathToIcfg(final IIcfg<INLOC> origIcfg, final Deque<INLOC> path,
			final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {

		final Deque<INLOC> open = new ArrayDeque<>();
		open.add(path.removeFirst());

		// Add the loopBody to the Icfg
		while (!open.isEmpty() && !path.isEmpty()) {

			final INLOC oldSource = open.removeFirst();
			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
				final INLOC oldTarget;

				// Check if transition is part of the path
				if (oldTransition.getTarget().equals(path.getFirst())) {
					oldTarget = (INLOC) oldTransition.getTarget();
					open.add(oldTarget);
				} else {
					oldTarget = origIcfg.getProcedureExitNodes().values().iterator().next();
				}

				// create new Nodes and Edges
				final OUTLOC newSource;
				newSource = lst.createNewLocation(oldSource);
				final OUTLOC newTarget = lst.createNewLocation(oldTarget);
				lst.createNewTransition(newSource, newTarget, oldTransition);
			}
			if (!path.isEmpty()) {
				path.removeFirst();
			}
		}
	}

	public IIcfg<OUTLOC> getLoop() {
		return mLoopIcfgs.getFirst();
	}

	public Deque<IIcfg<OUTLOC>> getAllResults() {
		return mLoopIcfgs;
	}

	public IIcfg<OUTLOC> rejoin(Term result, TermVariable n, Map<Term, Term> guardSubstitute) {
		Script script = mMgScript.getScript();
		UnmodifiableTransFormula loopTransFormula = 
				getLoop().getInitialNodes().iterator().next().getOutgoingEdges().iterator().next().getTransformula();
		
		//get LoopExit
		UnmodifiableTransFormula exitTransformula = null;
		for (final IcfgEdge transition : mLoopHead.getOutgoingEdges()) {
			//TODO kann es mehrere geben?
			if(!transition.getTarget().equals(mLoopHead)){
				exitTransformula = transition.getTransformula();
			}
		}
		
		//joint the TransFormula
		Map<Term, Term> substitute = new HashMap<>();
		Map<IProgramVar, TermVariable> outVars = new HashMap<>(exitTransformula.getOutVars());
		for(IProgramVar var : loopTransFormula.getOutVars().keySet()){
			if(exitTransformula.getInVars().containsKey(var)){
				substitute.put(exitTransformula.getInVars().get(var), loopTransFormula.getOutVars().get(var));
				if(exitTransformula.getInVars().get(var).equals(exitTransformula.getOutVars().get(var))){
					outVars.remove(var);
					outVars.put(var, loopTransFormula.getOutVars().get(var));
				}
			}else{
				outVars.put(var, loopTransFormula.getOutVars().get(var));
			}
		}
		final Substitution sub = new Substitution(mMgScript, substitute);
		Term transformedExitFormula = sub.transform(exitTransformula.getFormula());
		TransFormulaBuilder tfb = new TransFormulaBuilder(loopTransFormula.getInVars(),
				outVars, false, loopTransFormula.getNonTheoryConsts(), true, null, false);
		tfb.setFormula(script.term("and", transformedExitFormula, result));
		tfb.addAuxVar(n);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		UnmodifiableTransFormula loop = tfb.finishConstruction(mMgScript);
		
		//create icfg
		mOriginalIcfg.getIdentifier();
		final BasicIcfg<OUTLOC> resultIcfg =
				new BasicIcfg<>(mNewIcfgIdentifier, mOriginalIcfg.getCfgSmtToolkit(), mOutLocationClass);
		final TransformedIcfgBuilder<INLOC, OUTLOC> lst =
				new TransformedIcfgBuilder<>(mFunLocFac, mBacktranslationTracker, mTransformer, mOriginalIcfg, resultIcfg);
		processLocations(mOriginalIcfg.getInitialNodes(), lst, loop);
		lst.finish();
		return resultIcfg;
	}

	private void processLocations(final Set<INLOC> init, final TransformedIcfgBuilder<INLOC, OUTLOC> lst, UnmodifiableTransFormula loop) {
		final Deque<INLOC> open = new ArrayDeque<>(init);
		final Set<INLOC> closed = new HashSet<>();

		while (!open.isEmpty()) {
			final INLOC oldSource = open.removeFirst();
			if (!closed.add(oldSource)) {
				continue;
			}
			if(oldSource.equals(mLoopHead)){
				final OUTLOC newSource = lst.createNewLocation(oldSource);
				for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
					if(!oldTransition.getTarget().equals(mLoopHead)){
						final INLOC oldTarget = (INLOC) oldTransition.getTarget();
						open.add(oldTarget);
						final OUTLOC newTarget = lst.createNewLocation(oldTarget);					
						final IcfgInternalTransition newTransition = new IcfgInternalTransition(newSource, newTarget,
								getPayloadIfAvailable(oldTransition), loop);
						new Overapprox("loop acceleration: ... ", null).annotate(newTransition);
						newSource.addOutgoing(newTransition);
						newTarget.addIncoming(newTransition);
						mBacktranslationTracker.rememberRelation(oldTransition, newTransition);
						mLogger.info(newTransition.getTransformula());
					}
				}
			}else{
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