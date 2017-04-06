/*
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.LocationType;

public class Location {

	private final int mId;
	private final String mName;
	private String mInvariant;
	private String mFlow;
	private boolean mIsForbidden;
	private String mForbiddenConstraint;

	private final List<Transition> mOutgoingTransitions;
	private final List<Transition> mIncomingTransitions;

	private final double mXPos;
	private final double mYPos;

	protected Location(final int id) {
		this(id, new StringBuilder().append("loc_").append(id).toString());
	}

	protected Location(final LocationType location) {
		this(location.getId(), location.getName());
	}

	protected Location(final int id, final String name) {
		mName = name;
		mId = id;

		mOutgoingTransitions = new ArrayList<>();
		mIncomingTransitions = new ArrayList<>();

		mXPos = ((mId * 180) + 320);
		mYPos = ((mId * 140) + 60);
		mForbiddenConstraint = "";
	}

	public int getId() {
		return mId;
	}

	public String getName() {
		return mName;
	}

	protected void setInvariant(final String invariant) {
		if (invariant != null) {
			mInvariant = invariant.replaceAll("&&", "&");
		} else {
			mInvariant = "";
		}
	}

	protected void setFlow(final String flow) {
		if (flow != null && !"false".equals(flow)) {
			mFlow = flow.replaceAll("&&", "&");
		} else {
			mFlow = "";
		}

	}

	public String getInvariant() {
		return mInvariant;
	}

	public String getFlow() {
		return mFlow;
	}

	public boolean isForbidden() {
		return mIsForbidden;
	}

	public void setForbidden(final boolean isForbidden) {
		mIsForbidden = isForbidden;
	}

	public String getForbiddenConstraint() {
		return mForbiddenConstraint;
	}

	public void setForbiddenConstraint(final String forbidden) {
		if (mForbiddenConstraint.contains(forbidden)) {
			return;
		} else if (mForbiddenConstraint.isEmpty()) {
			mForbiddenConstraint = forbidden;
		} else {
			mForbiddenConstraint += "|" + forbidden;
		}
	}

	protected void addOutgoingTransition(final Transition t) {
		mOutgoingTransitions.add(t);
	}

	protected void addIncomingTransition(final Transition t) {
		mIncomingTransitions.add(t);
	}

	protected List<Transition> getOutgoingTransitions() {
		return mOutgoingTransitions;
	}

	protected List<Transition> getIncomingTransitions() {
		return mIncomingTransitions;
	}

	protected double getXPos() {
		return mXPos;
	}

	protected double getYPos() {
		return mYPos;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append(mName).append("(").append(mId).append(")").append(", Invariant: ").append(mInvariant);
		sb.append(", Flow: ").append(mFlow).append(", IsForbidden?: ").append(mIsForbidden);

		return sb.toString();
	}
}
