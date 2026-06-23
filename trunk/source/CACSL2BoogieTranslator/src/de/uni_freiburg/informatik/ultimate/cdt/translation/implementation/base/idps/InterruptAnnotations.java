/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 * Annotations for Boogie statements belonging to an interrupt-service-routine.
 */
public class InterruptAnnotations extends ModernAnnotations {
	private static final long serialVersionUID = 1L;
	private final ISRLocation mIsrLocation;
	private final int mIsrId;

	public InterruptAnnotations(final ISRLocation isrLocation, final int isrId) {
		mIsrLocation = isrLocation;
		mIsrId = isrId;
	}

	public InterruptAnnotations annotate(final IElement element) {
		return (InterruptAnnotations) element.getPayload().getAnnotations().put(InterruptAnnotations.class.getName(),
				this);
	}

	public int getIsrId() {
		return mIsrId;
	}

	public ISRLocation getIsrLocation() {
		return mIsrLocation;
	}

	public static InterruptAnnotations getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, InterruptAnnotations.class);
	}

	@Override
	public String toString() {
		final StringBuilder res = new StringBuilder("interrupt level: ");
		switch (getIsrLocation()) {
		case ENTRY:
			res.append("entry");
			break;
		case ISR:
			res.append("inner");
		default:
			break;
		}
		res.append(", interrupt id: ").append(getIsrId());
		return res.toString();
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other == this || other == null) {
			return this;
		}
		if (!(other instanceof InterruptAnnotations)) {
			return super.merge(other);
		}
		final InterruptAnnotations otherAnnotations = (InterruptAnnotations) other;
		final var otherLoc = otherAnnotations.getIsrLocation();
		final var otherId = otherAnnotations.getIsrId();
		if (getIsrLocation().equals(otherLoc) && getIsrId() == otherId) {
			return other;
		}
		assert otherId == getIsrId();
		return this;
	}

	public static boolean hasAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, InterruptAnnotations.class) != null;
	}

	public enum ISRLocation {
		ISR, ENTRY
	}
}
