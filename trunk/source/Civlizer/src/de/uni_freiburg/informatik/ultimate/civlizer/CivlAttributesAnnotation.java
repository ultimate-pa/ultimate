/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 * An internally-used annotation to mark Boogie AST nodes with attributes in places where our Boogie AST does not
 * support them, but Civl does.
 *
 * These annotations should be taken into account by {@link CivlOutput}. However, users of this class should check
 * whether support for the kind of AST nodes they are annotating is already implemented or not.
 */
class CivlAttributesAnnotation extends ModernAnnotations {
	private static final long serialVersionUID = 1L;

	private final Attribute[] mAttributes;

	public CivlAttributesAnnotation(final Attribute... attributes) {
		mAttributes = Objects.requireNonNull(attributes);
	}

	public static Attribute[] getAttributes(final BoogieASTNode node) {
		final var annotation = ModelUtils.getAnnotation(node, CivlAttributesAnnotation.class);
		if (annotation == null) {
			return null;
		}
		return annotation.mAttributes;
	}

	public void annotate(final BoogieASTNode node) {
		final var existing = ModelUtils.getAnnotation(node, CivlAttributesAnnotation.class);
		CivlAttributesAnnotation combined;
		if (existing == null) {
			combined = this;
		} else {
			combined = existing.merge(this);
		}
		node.getPayload().getAnnotations().put(CivlAttributesAnnotation.class.getName(), combined);
	}

	@Override
	public CivlAttributesAnnotation merge(final IAnnotations other) {
		if (!(other instanceof final CivlAttributesAnnotation otherAttributes)) {
			throw new UnmergeableAnnotationsException(this, other);
		}

		final var combined = new Attribute[mAttributes.length + otherAttributes.mAttributes.length];
		System.arraycopy(mAttributes, 0, combined, 0, mAttributes.length);
		System.arraycopy(otherAttributes.mAttributes, 0, combined, mAttributes.length,
				otherAttributes.mAttributes.length);
		return new CivlAttributesAnnotation(combined);
	}
}
