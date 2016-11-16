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

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

/**
 * A node in the abstract reachability graph that Kojak maintains.
 * Contains an IcfgLocation (earlier called ProgramPoint) that is annotated with a Predicate.
 * 
 * (Note that it is correct that this should not inherit from IcfgLocation because we may 
 *  have many instances of this class for a single program location -- which are annotated
 *  with different predicates
 *  -- writing this down here because of several attempts to go into that wrong direction)
 *
 * @author Alexander Nutz
 * @author Mohamed Sherif
 * @author Mostafa Mahmoud
 */
public class AnnotatedProgramPoint extends ModifiableExplicitEdgesMultigraph<AnnotatedProgramPoint, AppEdge,AnnotatedProgramPoint, AppEdge> {

	private static final long serialVersionUID = -4398335480646555023L;

	private final IPredicate _predicate;
	private final BoogieIcfgLocation _programPoint;

	private final HashSet<AppHyperEdge> _outgoingHyperEdges = new HashSet<AppHyperEdge>();

	/**
	 * Constructor of a new AnnotatedProgramPoint.
	 * 
	 * @param predicate
	 *            the annotation of the Node
	 * @param programPoint
	 *            the program point this APP represents
	 * @param isPEL
	 *            specifies whether or not this APP is considered to be an error
	 *            location
	 */

	public int _nodeID;

	public AnnotatedProgramPoint(IPredicate predicate, BoogieIcfgLocation programPoint) {
		_predicate = predicate;
		_programPoint = programPoint;
		_copies = new HashSet<AnnotatedProgramPoint>();
		_cloneSource = null;
	}

	/**
	 * Constructor that copies an old APP to a new one with the same
	 * programPoint, predicate, and isPseudoErrorLocation.
	 * 
	 * @param oldApp
	 *            the old APP that will be copied
	 */
	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp) {
		this(oldApp._predicate, oldApp._programPoint);
	}

	/**
	 * Constructor that copies an old APP and gives the copy a new predicate.
	 * 
	 * @param oldApp
	 *            the old APP that will be copied
	 * @param newPred
	 *            the predicate of the new copy
	 */
	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp, IPredicate newPred) {
		this(newPred, oldApp._programPoint);
	}

	/**
	 * Constructor that copies an old APP, copies its outgoing edges if
	 * specified to do so, and gives the copy a new predicate.
	 * 
	 * @param oldApp
	 *            the old APP that will be copied
	 * @param newPred
	 *            the predicate of the new copy
	 * @param copyOutgoingEdges
	 *            if true, the hyperedges will be copied
	 */
	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp, IPredicate newPred, boolean copyOutgoingEdges, int id) {
		this(oldApp, newPred);
		_nodeID = id;
		if (copyOutgoingEdges) {
			for (final AppEdge oldOutEdge : oldApp.getOutgoingEdges()) {
				if (oldOutEdge instanceof AppHyperEdge) {
					connectOutgoingReturn(((AppHyperEdge) oldOutEdge).getHier(),
							(Return) oldOutEdge.getStatement(), oldOutEdge.getTarget());
				} else {
					connectOutgoing(oldOutEdge.getStatement(), oldOutEdge.getTarget());
				}
			}

			for (final AppHyperEdge oldOutHypEdge : oldApp.getOutgoingHyperEdges()) {
				oldOutHypEdge.getSource().connectOutgoingReturn(this, (Return) oldOutHypEdge.getStatement(),
						oldOutHypEdge.getTarget());
			}
			oldApp._copies.add(this);
			_cloneSource = oldApp;
		}
	}

	public HashSet<AnnotatedProgramPoint> getNextClones() {
		return _copies;
	}

	public IPredicate getPredicate() {
		return _predicate;
	}

	public boolean isErrorLocation() {
		return _programPoint.isErrorLocation();
	}

	public BoogieIcfgLocation getProgramPoint() {
		return _programPoint;
	}

	public HashSet<AppHyperEdge> getOutgoingHyperEdges() {
		return _outgoingHyperEdges;
	}

	public AnnotatedProgramPoint getParentCopy() {
		return _cloneSource;
	}

	@Override
	public String toString() {
		final String ref = CodeChecker.objectReference(this);
		return _programPoint.toString() + ref.substring(Math.max(ref.length() - 3, 0)) + ":"
				+ _predicate.getFormula().toString();
	}

	public void connectOutgoing(CodeBlock statement, AnnotatedProgramPoint target) {
		assert !(statement instanceof Return);
		final AppEdge edge = new AppEdge(this, statement, target);
		mOutgoingEdges.add(edge);
		target.mIncomingEdges.add(edge);
	}

	public void connectOutgoingReturn(AnnotatedProgramPoint hier, Return returnStm, AnnotatedProgramPoint target) {
		final AppHyperEdge hyperEdge = new AppHyperEdge(this, hier, returnStm, target);
		hier._outgoingHyperEdges.add(hyperEdge);
		mOutgoingEdges.add(hyperEdge);
		target.mIncomingEdges.add(hyperEdge);
	}

	public AppEdge getEdge(AnnotatedProgramPoint target) {
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
		if (_cloneSource != null) {
			_cloneSource._copies.remove(this);
		}
	}

	private final HashSet<AnnotatedProgramPoint> _copies;
	private AnnotatedProgramPoint _cloneSource;
	// public void disconnectOutgoing(AppEdge outEdge) {
	// if (outEdge instanceof AppHyperEdge) {
	// ((AppHyperEdge) outEdge).hier._outgoingHyperEdges.remove(outEdge);
	// }
	// outEdge.getTarget().mIncomingEdges.remove(outEdge);//TODO: maybe make
	// them HashSets??
	// this.mOutgoingEdges.remove(outEdge);
	// }

	// formerly removed now there again.. --> impulse-specific stuff

	private final ArrayList<AnnotatedProgramPoint> copies = new ArrayList<AnnotatedProgramPoint>();
	private final ArrayList<AnnotatedProgramPoint> newCopies = new ArrayList<AnnotatedProgramPoint>();
	private AnnotatedProgramPoint cloneSource;

	/**
	 * Adds an APP to the list of new copies of this APP.
	 * 
	 * @param copy
	 *            the APP that will be added as a copy to this APP
	 */
	public void addCopy(AnnotatedProgramPoint copy) {
		newCopies.add(copy);
	}

	/**
	 * Moves new copies to the list of old copies.
	 */
	public void updateCopies() {
		copies.addAll(newCopies);
		newCopies.clear();
	}

	/**
	 * Sets the clone source of this APP. The clone source is the APP copies to
	 * form this APP.
	 * 
	 * @param source
	 *            the APP that should be declared to be the clone source
	 */
	public void setCloneSource(AnnotatedProgramPoint source) {
		cloneSource = source;
	}

	/**
	 * Gets a list of all the copies of this APP.
	 * 
	 * @return returns a list of copies of this APP
	 */
	public ArrayList<AnnotatedProgramPoint> getCopies() {
		final ArrayList<AnnotatedProgramPoint> ret = new ArrayList<AnnotatedProgramPoint>();
		ret.addAll(copies);
		ret.addAll(newCopies);
		return ret;
	}

	/**
	 * Gets a clone of the list of new copies of this APP.
	 * 
	 * @return returns a list of new copies of this APP
	 */
	public ArrayList<AnnotatedProgramPoint> getNewCopies() {
		final ArrayList<AnnotatedProgramPoint> ret = new ArrayList<AnnotatedProgramPoint>();
		ret.addAll(newCopies);
		return ret;
	}

	@Override
	public AnnotatedProgramPoint getLabel() {
		return this;
	}

}
