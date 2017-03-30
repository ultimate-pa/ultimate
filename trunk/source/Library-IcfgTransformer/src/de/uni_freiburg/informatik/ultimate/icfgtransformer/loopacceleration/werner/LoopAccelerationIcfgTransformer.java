
/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * A basic IcfgTransformer that applies the {@link ExampleLoopAccelerationTransformulaTransformer}, i.e., replaces all
 * transformulas of an {@link IIcfg} with a new instance.
 * +
 * First tries for loop acceleration.
 *
 * @param <INLOC>
 *            The type of the locations of the old IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the transformed IIcfg.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Jonas Werner (jonaswerner95@gmail.com)
 *
 */
public class LoopAccelerationIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> {

	private final ILogger mLogger;	

	private final Deque<Deque<Backbone>> mBackBones;
	
	private final LoopDetector<INLOC> mLoopDetector;

	@SuppressWarnings("unused")
	public LoopAccelerationIcfgTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker,
			final Class<OUTLOC> outLocationClass, final String newIcfgIdentifier,
			final ITransformulaTransformer transformer) {

		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mLogger = Objects.requireNonNull(logger);
		
		mLoopDetector = new LoopDetector<>(mLogger, origIcfg);
		
		mBackBones = new ArrayDeque<>();
		
		IIcfg<OUTLOC> result = transform(originalIcfg, newIcfgIdentifier, outLocationClass);

	}

	private IIcfg<OUTLOC> transform(final IIcfg<INLOC> originalIcfg, final String newIcfgIdentifier,
			final Class<OUTLOC> outLocationClass) {
		
		mLogger.debug("transforming...");
		
		getBackbones();
		
		final BasicIcfg<OUTLOC> resultIcfg =
				new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);

		
		
		return resultIcfg;
	}
	
	private void getBackbones() {
		
		final Deque<Deque<IcfgEdge>> loopBodies = mLoopDetector.getLoopBodies();
		
		mLogger.debug("getting Backbones...");
		
		if(loopBodies.isEmpty()) {
			// something
		}

		// @todo finding more than one backbone...
		for (final Deque<IcfgEdge> loopBody : loopBodies) {
			
			final Deque<Backbone> backBones = new ArrayDeque<>();
			final IcfgLocation loopHeader = loopBody.getFirst().getSource();
			
			Deque<IcfgEdge> possibleBackbone = new ArrayDeque<>();
			IcfgEdge current = loopBody.getFirst();
			possibleBackbone.addFirst(current);
			for (IcfgEdge transition : loopBody) {
				if (current.getTarget() == loopHeader) {
					
					Backbone backbone = new Backbone(possibleBackbone);
					
					backBones.addLast(backbone);
					break;
				}
				
				if (transition.getSource() == current.getTarget()) {
					possibleBackbone.addLast(transition);
					current = transition;
				}
			}
			mBackBones.addLast(backBones);
		}
	}
	
	/*
	private void executeBackbones() {
		
	}
	
	private void computeSummary() {
		
	}
	
	*/


	/**
	 * Interface that describes a factory which creates locations for an {@link IIcfg} based on an old location.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 * @param <INLOC>
	 *            The type of the old locations.
	 * @param <OUTLOC>
	 *            The type of locations that should be produced.
	 */
	@FunctionalInterface
	public static interface ILocationFactory<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> {
		OUTLOC createLocation(final INLOC oldLocation, final String debugIdentifier, final String procedure);
	}

	@FunctionalInterface
	public static interface IBacktranslationTracker {
		void rememberRelation(final IIcfgTransition<?> oldTransition, final IIcfgTransition<?> newTransition);
	}

}
