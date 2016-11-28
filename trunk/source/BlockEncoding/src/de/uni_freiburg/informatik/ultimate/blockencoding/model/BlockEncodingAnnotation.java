/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncoding plug-in.
 *
 * The ULTIMATE BlockEncoding plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncoding plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncoding plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncoding plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncoding plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.model;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding.Activator;

public class BlockEncodingAnnotation extends ModernAnnotations {

	private static final long serialVersionUID = 1L;

	private final MinimizedNode mNode;

	public BlockEncodingAnnotation(final MinimizedNode node) {
		mNode = node;
	}

	public MinimizedNode getNode() {
		return mNode;
	}

	public static void addAnnotation(final IElement elem, final IAnnotations annot) {
		elem.getPayload().getAnnotations().put(Activator.PLUGIN_ID, annot);
	}

	public static BlockEncodingAnnotation getAnnotation(final IElement elem) {
		if (elem.hasPayload()) {
			final IAnnotations rtr = elem.getPayload().getAnnotations().get(Activator.PLUGIN_ID);
			if (rtr != null) {
				return (BlockEncodingAnnotation) rtr;
			}
		}
		return null;
	}
}
