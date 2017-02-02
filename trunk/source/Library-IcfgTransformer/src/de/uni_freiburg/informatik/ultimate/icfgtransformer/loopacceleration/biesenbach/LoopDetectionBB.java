package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * Extracts the loops from an {@link IIcfg}.
 *
 * @param <INLOC>
 *            The type of the locations of the IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the IIcfg with only loops left.
 *
 * @authot Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Ben Biesenbach (Ben.Biesenbach@gmx.de)
 */
public class LoopDetectionBB<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> {

	@SuppressWarnings("unused")
	private final ILogger mLogger;
	private final BasicIcfg<OUTLOC> mResultIcfg;
	private final Map<INLOC, OUTLOC> mOldLoc2NewLoc;
	private final Map<IIcfgCallTransition<INLOC>, IcfgCallTransition> mOldCalls2NewCalls;
	private final ITransformulaTransformer mTransformer;
	private IBacktranslationTracker mBacktranslationTracker;
	private ILocationFactory<INLOC, OUTLOC> mLocationFactory;

	/**
	 * Extracts the loops from an {@link IIcfg}.
	 * @param logger
	 * @param originalIcfg
	 * @param outLocationClass
	 * @param funLocFac
	 * @param newIcfgIdentifier
	 * @param transformer
	 * @param backtranslationTracker
	 */
	public LoopDetectionBB(final ILogger logger, final IIcfg<INLOC> originalIcfg, final Class<OUTLOC> outLocationClass, 
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final String newIcfgIdentifier,
			final ITransformulaTransformer transformer, final IBacktranslationTracker backtranslationTracker) {
		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mLogger = Objects.requireNonNull(logger);
		mLocationFactory = Objects.requireNonNull(funLocFac);
		mOldLoc2NewLoc = new HashMap<>();
		mOldCalls2NewCalls = new HashMap<>();
		mBacktranslationTracker = backtranslationTracker;
		mTransformer = Objects.requireNonNull(transformer);
		mResultIcfg = new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);

		// perform transformation last
		getLoop(origIcfg, Objects.requireNonNull(newIcfgIdentifier),Objects.requireNonNull(outLocationClass));
	}
	
	/*
	 * ---------second attempt----------
	 * (extracts the loops of a program)
	 */
	
	private void getLoop(final IIcfg<INLOC> originalIcfg, final String newIcfgIdentifier,
			final Class<OUTLOC> outLocationClass){
		for(final INLOC loopHead : originalIcfg.getLoopLocations()){
			Deque<INLOC> path = new ArrayDeque<>();
			path.addLast(loopHead);
			transformPathToIcfg(getLoopPath(path),originalIcfg,newIcfgIdentifier,outLocationClass);
		}
	}

	@SuppressWarnings("unchecked")
	private Deque<INLOC> getLoopPath(Deque<INLOC> path){
		Deque<INLOC> loopPath = null;
		for (final IcfgEdge transition : path.getLast().getOutgoingEdges()) {
			if (transition.getTarget().equals(path.getFirst())) {
				path.addLast((INLOC) transition.getTarget());
				return path;
			}
			Deque<INLOC> newPath = new ArrayDeque<>(path);
			newPath.addLast((INLOC) transition.getTarget());
			Deque<INLOC> returnedPath = getLoopPath(newPath);
			if (returnedPath != null) {
				loopPath = returnedPath;
			}
		}
		return loopPath;
	}
	
	@SuppressWarnings("unchecked")
	private void transformPathToIcfg(Deque<INLOC> path,IIcfg<INLOC> originalIcfg, final String newIcfgIdentifier,
			final Class<OUTLOC> outLocationClass){

		final Set<INLOC> init = originalIcfg.getInitialNodes();
		final Deque<INLOC> open = new ArrayDeque<>(init);
		final Set<INLOC> closed = new HashSet<>();

		//Connect initial nodes with loopHead
		final INLOC oldMainENTRY = open.removeFirst();
		closed.add(oldMainENTRY);
		final OUTLOC newMainENTRY = createNewLocation(originalIcfg, mResultIcfg, oldMainENTRY);
		final OUTLOC newLoopHead = createNewLocation(originalIcfg, mResultIcfg, path.getFirst());
		//TODO Which transition is needed? Or is there even a way without mainENTRY?
		final IcfgEdge newTransitionLH = new IcfgInternalTransition(newMainENTRY, newLoopHead, null, null);
		newMainENTRY.addOutgoing(newTransitionLH);
		newLoopHead.addIncoming(newTransitionLH);
		open.add(path.getFirst());
		path.removeFirst();
		
		//Add the loopBody to the Icfg
		while (!open.isEmpty()) {
			final INLOC oldSource = open.removeFirst();
			if (!closed.add(oldSource)) {
				continue;
			}
			
			final OUTLOC newSource = createNewLocation(originalIcfg, mResultIcfg, oldSource);
			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
				final INLOC oldTarget;
				//Check if transition is part of the path
				if (oldTransition.getTarget().equals(path.getFirst())) {
					oldTarget = (INLOC) oldTransition.getTarget();
				} else {
					//TODO Which transition is needed for the exit? If there are multiple exits, which are the right ones?
					oldTarget = originalIcfg.getProcedureExitNodes().values().iterator().next();
				}
				open.add(oldTarget);
				final OUTLOC newTarget = createNewLocation(originalIcfg, mResultIcfg, oldTarget);
				final IcfgEdge newTransition;
				if (oldTransition instanceof IIcfgInternalTransition) {
					newTransition = createNewLocalTransition(newSource, newTarget,
							(IIcfgInternalTransition<INLOC>) oldTransition);
				} else if (oldTransition instanceof IIcfgCallTransition) {
					newTransition =
							createNewCallTransition(newSource, newTarget, (IIcfgCallTransition<INLOC>) oldTransition);
				} else if (oldTransition instanceof IIcfgReturnTransition) {
					newTransition = createNewReturnTransition(newSource, newTarget,
							(IIcfgReturnTransition<INLOC, ?>) oldTransition);
				} else {
					throw new IllegalArgumentException("Unknown edge type " + oldTransition.getClass().getSimpleName());
				}
				newSource.addOutgoing(newTransition);
				newTarget.addIncoming(newTransition);
				mBacktranslationTracker.rememberRelation(oldTransition, newTransition);
			}
			if (!path.isEmpty()) {
				path.removeFirst();
			}
		}
	}
	
	private IcfgReturnTransition createNewReturnTransition(final IcfgLocation source, final IcfgLocation target,
			final IIcfgReturnTransition<INLOC, ?> oldTransition) {
		final IIcfgCallTransition<INLOC> oldCorrespondingCall = oldTransition.getCorrespondingCall();
		final IcfgCallTransition newCorrespondingCall = mOldCalls2NewCalls.get(oldCorrespondingCall);
		assert newCorrespondingCall != null : "The Icfg has been traversed out of order "
				+ "(found return before having found the corresponding call)";
		final UnmodifiableTransFormula retAssign = mTransformer.transform(oldTransition.getAssignmentOfReturn());
		final UnmodifiableTransFormula localVarAssign =
				mTransformer.transform(oldTransition.getLocalVarsAssignmentOfCall());
		return new IcfgReturnTransition(source, target, newCorrespondingCall, getPayloadIfAvailable(oldTransition),
				retAssign, localVarAssign);
	}

	private IcfgCallTransition createNewCallTransition(final IcfgLocation source, final IcfgLocation target,
			final IIcfgCallTransition<INLOC> oldTransition) {
		final UnmodifiableTransFormula unmodTf = mTransformer.transform(oldTransition.getLocalVarsAssignment());
		final IcfgCallTransition rtr =
				new IcfgCallTransition(source, target, getPayloadIfAvailable(oldTransition), unmodTf);
		// cache the created call for usage during return creation
		mOldCalls2NewCalls.put(oldTransition, rtr);
		return rtr;
	}

	private IcfgInternalTransition createNewLocalTransition(final IcfgLocation source, final IcfgLocation target,
			final IIcfgInternalTransition<INLOC> oldTransition) {
		final UnmodifiableTransFormula unmodTf = mTransformer.transform(oldTransition.getTransformula());
		return new IcfgInternalTransition(source, target, getPayloadIfAvailable(oldTransition), unmodTf);
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
	
	private OUTLOC createNewLocation(final IIcfg<INLOC> originalIcfg, final BasicIcfg<OUTLOC> resultIcfg,
			final INLOC oldLoc) {
		final OUTLOC alreadyCreated = mOldLoc2NewLoc.get(oldLoc);
		if (alreadyCreated != null) {
			// was already created, no need to re-add to the result icfg
			return alreadyCreated;
		}

		final String proc = oldLoc.getProcedure();
		final OUTLOC freshLoc = mLocationFactory.createLocation(oldLoc, oldLoc.getDebugIdentifier(), proc);

		// determine attributes of location
		final boolean isInitial = originalIcfg.getInitialNodes().contains(oldLoc);
		final Set<INLOC> errorLocs = originalIcfg.getProcedureErrorNodes().get(proc);
		final boolean isError = errorLocs != null && errorLocs.contains(oldLoc);
		final boolean isProcEntry = oldLoc.equals(originalIcfg.getProcedureEntryNodes().get(proc));
		final boolean isProcExit = oldLoc.equals(originalIcfg.getProcedureExitNodes().get(proc));
		final boolean isLoopLocation = originalIcfg.getLoopLocations().contains(oldLoc);

		// add fresh location to resultIcfg
		resultIcfg.addLocation(freshLoc, isInitial, isError, isProcEntry, isProcExit, isLoopLocation);

		// cache created IcfgLocation
		mOldLoc2NewLoc.put(oldLoc, freshLoc);

		return freshLoc;
	}
	
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}
	
	/*  ----------first attempt----------
	   (only checks if program has a loop)
	
	public boolean isLooped(final IIcfg<INLOC> originalIcfg) {
		final Set<INLOC> init = originalIcfg.getInitialNodes();
		final Deque<INLOC> queue = new ArrayDeque<>(init);
		final Deque<INLOC> marked = new ArrayDeque<>();
		
		while (!queue.isEmpty()) {
			final INLOC node = queue.removeFirst();
			if(recursivHelper(node, marked)){
				return true;
			}
		}
		return false;
	}
	
	@SuppressWarnings("unchecked")
	private boolean recursivHelper(INLOC node, Deque<INLOC> marked){
		if (marked.contains(node)) {
			return true;
		}
		marked.add(node);
		for (final IcfgEdge transition : node.getOutgoingEdges()) {
			if(recursivHelper((INLOC) transition.getTarget(), new ArrayDeque<>(marked))){
				return true;
			}
		}
		return false;
	}
	*/
}