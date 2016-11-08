/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.models;

import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;

/***
 * 
 * This class represents the edges for the Ultimate visualization structure. For more details, see
 * {@link VisualizationNode}.
 * 
 * @author dietsch
 * 
 * @see VisualizationNode
 * @see BaseMultigraphEdge
 */
public final class VisualizationEdge
		extends BaseMultigraphEdge<VisualizationNode, VisualizationEdge, VisualizationNode, VisualizationEdge> {

	private final Object mBacking;

	protected VisualizationEdge(final VisualizationNode source, final VisualizationNode target, final IPayload payload, final Object backing) {
		super(source, target, payload);
		mBacking = backing;
	}

	protected VisualizationEdge(final VisualizationNode source, final VisualizationNode target, final Object backing) {
		super(source, target);
		mBacking = backing;
	}

	private static final long serialVersionUID = 1L;

	@Override
	public String toString() {
		if (mBacking == null) {
			return "";
		} else {

			return mBacking.toString();
		}
	}

	public Object getBacking() {
		return mBacking;
	}

	@Override
	public boolean equals(final Object obj) {
		if (obj instanceof VisualizationEdge) {
			final VisualizationEdge other = (VisualizationEdge) obj;
			if (mBacking == null && other.mBacking == null) {
				return super.equals(obj);
			} else if (mBacking == null) {
				return false;
			} else {
				return mBacking.equals(other.mBacking);
			}
		}
		return super.equals(obj);
	}

	@Override
	public int hashCode() {
		if (mBacking == null) {
			return super.hashCode();
		} else {
			return mBacking.hashCode();
		}
	}

	@Override
	public VisualizationEdge getLabel() {
		return this;
	}

}
