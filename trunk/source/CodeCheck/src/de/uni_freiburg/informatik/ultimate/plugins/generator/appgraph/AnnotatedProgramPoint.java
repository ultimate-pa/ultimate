/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Mohamed Sherif
 * Copyright (C) 2014-2015 Mostafa Mahmoud Amin
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CodeCheck plug-in.
 * 
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * A node in the abstract reachability graph that Kojak maintains. Contains an IcfgLocation (earlier called
 * ProgramPoint) that is annotated with a Predicate.
 * 
 * (Note that it is correct that this should not inherit from IcfgLocation because we may have many instances of this
 * class for a single program location -- which are annotated with different predicates -- writing this down here
 * because of several attempts to go into that wrong direction)
 *
 * @author Alexander Nutz
 * @author Mohamed Sherif
 * @author Mostafa Mahmoud
 */
public class AnnotatedProgramPoint
		extends ModifiableExplicitEdgesMultigraph<AnnotatedProgramPoint, AppEdge, AnnotatedProgramPoint, AppEdge> {

	private static final long serialVersionUID = -4398335480646555023L;

	private final IPredicate mPredicate;
	private final IcfgLocation mProgramPoint;
	private final boolean mIsErrorLoc;

	private final Set<AppHyperEdge> mOutgoingHyperEdges;
	private final Set<AnnotatedProgramPoint> mCopies;
	private final Set<AnnotatedProgramPoint> mNewCopies;

	private AnnotatedProgramPoint mCloneSource;
	private final int mNodeID;

	public AnnotatedProgramPoint(final IPredicate predicate, final IcfgLocation programPoint, final boolean isErrorLoc,
			final int nodeId) {
		mPredicate = predicate;
		mProgramPoint = programPoint;
		mIsErrorLoc = isErrorLoc;
		mNodeID = nodeId;
		mOutgoingHyperEdges = new HashSet<>();
		mCopies = new HashSet<>();
		mNewCopies = new HashSet<>();
		mCloneSource = null;
	}

	/**
	 * Constructor of a new AnnotatedProgramPoint.
	 * 
	 * @param predicate
	 *            the annotation of the Node
	 * @param programPoint
	 *            the program point this APP represents
	 * @param isPEL
	 *            specifies whether or not this APP is considered to be an error location
	 */
	public AnnotatedProgramPoint(final IPredicate predicate, final IcfgLocation programPoint,
			final boolean isErrorLoc) {
		this(predicate, programPoint, isErrorLoc, 0);
	}

	/**
	 * Constructor that copies an old APP to a new one with the same programPoint, predicate, and id.
	 * 
	 * @param oldApp
	 *            the old APP that will be copied
	 */
	public AnnotatedProgramPoint(final AnnotatedProgramPoint oldApp) {
		this(oldApp.mPredicate, oldApp.mProgramPoint, oldApp.mIsErrorLoc, oldApp.mNodeID);
	}

	/**
	 * Constructor that copies an old APP and gives the copy a new predicate.
	 * 
	 * @param oldApp
	 *            the old APP that will be copied
	 * @param newPred
	 *            the predicate of the new copy
	 */
	public AnnotatedProgramPoint(final AnnotatedProgramPoint oldApp, final IPredicate newPred) {
		this(newPred, oldApp.mProgramPoint, oldApp.mIsErrorLoc, oldApp.mNodeID);
	}

	/**
	 * Constructor that copies an old APP, copies its outgoing edges if specified to do so, and gives the copy a new
	 * predicate.
	 * 
	 * @param oldApp
	 *            the old APP that will be copied
	 * @param newPred
	 *            the predicate of the new copy
	 * @param copyOutgoingEdges
	 *            if true, the hyperedges will be copied
	 */
	public AnnotatedProgramPoint(final AnnotatedProgramPoint oldApp, final IPredicate newPred,
			final boolean copyOutgoingEdges, final int id) {
		this(newPred, oldApp.mProgramPoint, oldApp.mIsErrorLoc, id);
		if (copyOutgoingEdges) {
			for (final AppEdge oldOutEdge : oldApp.getOutgoingEdges()) {
				if (oldOutEdge instanceof AppHyperEdge) {
					connectOutgoingReturn(((AppHyperEdge) oldOutEdge).getHier(),
							(IIcfgReturnTransition<?, ?>) oldOutEdge.getStatement(), oldOutEdge.getTarget());
				} else {
					connectOutgoing(oldOutEdge.getStatement(), oldOutEdge.getTarget());
				}
			}

			for (final AppHyperEdge oldOutHypEdge : oldApp.getOutgoingHyperEdges()) {
				oldOutHypEdge.getSource().connectOutgoingReturn(this,
						(IIcfgReturnTransition<?, ?>) oldOutHypEdge.getStatement(), oldOutHypEdge.getTarget());
			}
			oldApp.mCopies.add(this);
			mCloneSource = oldApp;
		}
	}

	public Set<AnnotatedProgramPoint> getNextClones() {
		return mCopies;
	}

	public IPredicate getPredicate() {
		return mPredicate;
	}

	public boolean isErrorLocation() {
		return mIsErrorLoc;
	}

	public IcfgLocation getProgramPoint() {
		return mProgramPoint;
	}

	public Set<AppHyperEdge> getOutgoingHyperEdges() {
		return mOutgoingHyperEdges;
	}

	public AnnotatedProgramPoint getParentCopy() {
		return mCloneSource;
	}

	@Override
	public String toString() {
		final String ref = Integer.toHexString(System.identityHashCode(this));
		return mProgramPoint.toString() + ref.substring(Math.max(ref.length() - 3, 0)) + ":"
				+ mPredicate.getFormula().toString();
	}

	public void connectOutgoing(final IIcfgTransition<?> transition, final AnnotatedProgramPoint target) {
		assert !(transition instanceof IIcfgReturnTransition<?, ?>);
		final AppEdge edge = new AppEdge(this, transition, target);
		mOutgoingEdges.add(edge);
		target.mIncomingEdges.add(edge);
	}

	public void connectOutgoingReturn(final AnnotatedProgramPoint hier, final IIcfgReturnTransition<?, ?> returnStm,
			final AnnotatedProgramPoint target) {
		final AppHyperEdge hyperEdge = new AppHyperEdge(this, hier, returnStm, target);
		hier.mOutgoingHyperEdges.add(hyperEdge);
		mOutgoingEdges.add(hyperEdge);
		target.mIncomingEdges.add(hyperEdge);
	}

	public AppEdge getEdge(final AnnotatedProgramPoint target) {
		for (final AppEdge edge : mOutgoingEdges) {
			if (edge.getTarget() == target) {
				return edge;
			}
		}
		return null;
	}

	public void isolateNode() {
		final AppEdge[] edges = getIncomingEdges().toArray(new AppEdge[] {});
		for (final AppEdge edge : edges) {
			edge.disconnect();
		}
		if (mCloneSource != null) {
			mCloneSource.mCopies.remove(this);
		}
	}

	/**
	 * Adds an APP to the list of new copies of this APP.
	 * 
	 * @param copy
	 *            the APP that will be added as a copy to this APP
	 */
	public void addCopy(final AnnotatedProgramPoint copy) {
		mNewCopies.add(copy);
	}

	/**
	 * Moves new copies to the list of old copies.
	 */
	public void updateCopies() {
		mCopies.addAll(mNewCopies);
		mNewCopies.clear();
	}

	/**
	 * Sets the clone source of this APP. The clone source is the APP copies to form this APP.
	 * 
	 * @param source
	 *            the APP that should be declared to be the clone source
	 */
	public void setCloneSource(final AnnotatedProgramPoint source) {
		mCloneSource = source;
	}

	/**
	 * Gets a list of all the copies of this APP.
	 * 
	 * @return returns a list of copies of this APP
	 */
	public List<AnnotatedProgramPoint> getCopies() {
		final ArrayList<AnnotatedProgramPoint> ret = new ArrayList<>();
		ret.addAll(mCopies);
		ret.addAll(mNewCopies);
		return ret;
	}

	/**
	 * Gets a clone of the list of new copies of this APP.
	 * 
	 * @return returns a list of new copies of this APP
	 */
	public List<AnnotatedProgramPoint> getNewCopies() {
		final ArrayList<AnnotatedProgramPoint> ret = new ArrayList<>();
		ret.addAll(mNewCopies);
		return ret;
	}

	@Override
	public AnnotatedProgramPoint getLabel() {
		return this;
	}

	public int getNodeId() {
		return mNodeID;
	}

}
