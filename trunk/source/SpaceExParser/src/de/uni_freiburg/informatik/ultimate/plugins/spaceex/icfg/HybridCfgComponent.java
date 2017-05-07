/*
 * Copyright (C) 2017 Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 *
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Class that represents a ICFG component of a HybridAutomata component. It is used for the translation from
 * HybridAutomaton to ICFG
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class HybridCfgComponent {
	
	private final String mId;
	private final IcfgLocation mStartLocation;
	private final IcfgLocation mEndLocation;
	private final List<IcfgLocation> mLocations;
	private final List<IcfgInternalTransition> mTransitions;
	private final String mLocationInvariant;
	
	public HybridCfgComponent(final String string, final IcfgLocation start, final IcfgLocation end,
			final List<IcfgLocation> locations, final List<IcfgInternalTransition> transitions,
			final String invariant) {
		mId = string;
		mStartLocation = start;
		mEndLocation = end;
		mLocations = locations;
		mTransitions = transitions;
		mLocationInvariant = invariant;
	}
	
	public String getId() {
		return mId;
	}
	
	public IcfgLocation getStart() {
		return mStartLocation;
	}
	
	public IcfgLocation getEnd() {
		return mEndLocation;
	}
	
	public List<IcfgLocation> getLocations() {
		return mLocations;
	}
	
	public List<IcfgInternalTransition> getTransitions() {
		return mTransitions;
	}
	
	public String getLocationInvariant() {
		return mLocationInvariant;
	}
	
	@Override
	public String toString() {
		String comp = "\n";
		final String indent = "   ";
		comp += "ID: " + mId + "\n";
		comp += "Start: " + mStartLocation.getDebugIdentifier() + "\n";
		for (final IcfgEdge trans : mStartLocation.getOutgoingEdges()) {
			comp += indent + "** outgoing:" + "(" + trans.getSource().getDebugIdentifier() + "-->"
					+ trans.getTarget().getDebugIdentifier() + ")\n";
		}
		for (final IcfgEdge trans : mStartLocation.getIncomingEdges()) {
			comp += indent + "** incoming:" + "(" + trans.getSource().getDebugIdentifier() + "-->"
					+ trans.getTarget().getDebugIdentifier() + ")\n";
		}
		comp += "End: " + mEndLocation.getDebugIdentifier() + "\n";
		for (final IcfgEdge trans : mEndLocation.getOutgoingEdges()) {
			comp += indent + "** outgoing:" + "(" + trans.getSource().getDebugIdentifier() + "-->"
					+ trans.getTarget().getDebugIdentifier() + ")\n";
		}
		for (final IcfgEdge trans : mEndLocation.getIncomingEdges()) {
			comp += indent + "** incoming:" + "(" + trans.getSource().getDebugIdentifier() + "-->"
					+ trans.getTarget().getDebugIdentifier() + ")\n";
		}
		comp += "locations: \n";
		for (final IcfgLocation icfgLocation : mLocations) {
			comp += indent + "* Loc:" + icfgLocation.getDebugIdentifier() + "\n";
			for (final IcfgEdge trans : icfgLocation.getOutgoingEdges()) {
				comp += indent + "** outgoing:" + "(" + trans.getSource().getDebugIdentifier() + "-->"
						+ trans.getTarget().getDebugIdentifier() + ")\n";
			}
			for (final IcfgEdge trans : icfgLocation.getIncomingEdges()) {
				comp += indent + "** incoming:" + "(" + trans.getSource().getDebugIdentifier() + "-->"
						+ trans.getTarget().getDebugIdentifier() + ")\n";
			}
		}
		comp += "transitions: \n";
		for (final IcfgInternalTransition trans : mTransitions) {
			comp += indent + "* (" + trans.getSource().getDebugIdentifier() + "-->"
					+ trans.getTarget().getDebugIdentifier() + ")\n";
		}
		return comp;
	}
	
}
