/*
 * Copyright (C) 2017 Ben Biesenbach (ben.biesenbach@gmx.de)
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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * A {@link IIcfgTransformer} that accelerates the first loop if finds and creates a new accelerated {@link IIcfg}.
 *
 * @param <INLOC>
 *            The type of the locations of the old IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the transformed IIcfg.
 *
 * @author Ben Biesenbach (Ben.Biesenbach@gmx.de)
 *
 */
public class IcfgLoopAcceleration<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {
	
	final ILogger mLogger;
	final IIcfg<INLOC> mOriginalIcfg;
	final Class<OUTLOC> mOutLocationClass;
	final ILocationFactory<INLOC, OUTLOC> mFunLocFac;
	final String mNewIcfgIdentifier;
	final ITransformulaTransformer mTransformer;
	final IBacktranslationTracker mBacktranslationTracker;
	final IUltimateServiceProvider mServices;
	final LoopAccelerationOptions mOption;

	/**
	 * Different options for the loop acceleration
	 *
	 * @author Ben Biesenbach (Ben.Biesenbach@gmx.de)
	 *
	 */
	public enum LoopAccelerationOptions {
		/**
		 * If the {@link IIcfg} contains a loop that cannot be accelerated with a valid underapproximation, throw an
		 * exception.
		 */
		THROW_EXEPTION,

		/**
		 * If the acceleration contains an overapproximation (i.e., some variables had to be overapproximated with *),
		 * add the acceleration and mark it as overapproximation. If a loop can -- for some reason -- not be
		 * accelerated, just ignore it with a warning.
		 */
		MARK_AS_OVERAPPROX,

		/**
		 * Only add an acceleration if it is a valid underapproximation and ignore all other loops.
		 */
		DO_NOT_ACCELERATE
	}

	private IIcfg<OUTLOC> mResultIcfg;

	/**
	 * Default constructor.
	 *
	 * @param logger
	 * @param originalIcfg
	 * @param outLocationClass
	 * @param funLocFac
	 * @param newIcfgIdentifier
	 * @param transformer
	 * @param backtranslationTracker
	 * @param services
	 * @param replacementVarFactory
	 * @param option
	 */
	public IcfgLoopAcceleration(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final Class<OUTLOC> outLocationClass, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer,
			final IBacktranslationTracker backtranslationTracker, final IUltimateServiceProvider services,
			final LoopAccelerationOptions option) {
		
		//Setup
		mLogger = logger;
		mOriginalIcfg = originalIcfg;
		mOutLocationClass = outLocationClass;
		mFunLocFac = funLocFac;
		mNewIcfgIdentifier = newIcfgIdentifier;
		mTransformer = transformer;
		mBacktranslationTracker = backtranslationTracker;
		mServices = services;
		mOption = option;
		
		//printDetailedGraph(originalIcfg.getInitialNodes());
		
		if(option.equals(LoopAccelerationOptions.MARK_AS_OVERAPPROX)){
			mResultIcfg = accelerat();
			//printDetailedGraph(mResultIcfg.getInitialNodes());
		}else{
			mResultIcfg =  (IIcfg<OUTLOC>) originalIcfg;
		}
	}
	
	
	public <T> void printDetailedGraph(final Set<T> init){
		Deque<IcfgLocation> open = new ArrayDeque<>();
		Deque<IcfgLocation> marked = new ArrayDeque<>();
		for(T i : init){
			open.add((IcfgLocation) i);
		}
		while(!open.isEmpty()){
			IcfgLocation node = open.pop();
			mLogger.info("node: " + node);
			for(IcfgEdge edge : node.getOutgoingEdges()){
				 IcfgLocation target = edge.getTarget();
				 mLogger.info(edge.getTransformula().getFormula().toStringDirect() + " -> " + target);
				 if(!marked.contains(target)){
					 open.add(target);
					 marked.add(target);
				 }
			 }
		 }
	}
	
	@SuppressWarnings("unchecked")
	private IIcfg<OUTLOC> accelerat() {
		IIcfg<INLOC> originalIcfgCoppy = mOriginalIcfg;
		ManagedScript mMgScript = originalIcfgCoppy.getCfgSmtToolkit().getManagedScript();
		int loopCounter = 0;
		
		// get the loops to accelerate
		LoopExtraction<INLOC, OUTLOC> loopExtraction = new LoopExtraction<>(mLogger, mOriginalIcfg);
		for(SimpleLoop loop : loopExtraction.getLoopTransFormulas()){
			boolean out = (loop.mLoopTransFormula.getAssignedVars().size() == loop.mLoopTransFormula.getOutVars().size());
			boolean in = (loop.mLoopTransFormula.getAssignedVars().size() == loop.mLoopTransFormula.getInVars().size());
			if(!(in && out)){
				mLogger.info(loop.mLoopTransFormula.getAssignedVars() + "in != out!" + loop.mLoopTransFormula.getOutVars());
				continue;
			}
			loopCounter += 1;
			// create the matrix
			final MatrixBB matrix = new LoopAccelerationMatrix<>(mLogger, loop.mLoopTransFormula, mMgScript).getResult();
			// calculate the alphas
			final AlphaSolver<INLOC> alphaSolver =
					new AlphaSolver<>(mLogger, loop.mLoopTransFormula, mMgScript, matrix.getMatrix(), matrix.getLGS(), mServices, loopCounter);
			// add guard and final icfg
			final LoopInsertion<INLOC, OUTLOC> loopInsertion = new LoopInsertion<>(mLogger, originalIcfgCoppy,
					mOutLocationClass, mFunLocFac, mNewIcfgIdentifier, mTransformer, mBacktranslationTracker, mServices);
			originalIcfgCoppy = (IIcfg<INLOC>) loopInsertion.rejoin2(loop, alphaSolver.getResult(), alphaSolver.getValues(), alphaSolver.getN());
		}
		return (IIcfg<OUTLOC>) originalIcfgCoppy;
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}
}