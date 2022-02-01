/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.core.lib.models.annotation;

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;

/**
 * Annotation for transition (e.g., CodeBlock) that indicates that it was not build by a semantics preserving
 * translation but by an overapproximation. This allows model checkers to report <i>unknown</i> instead of <i>unsafe</i>
 * for traces that contain elements with this annotation.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class Overapprox extends ModernAnnotations {

	private static final long serialVersionUID = -575969312624287029L;
	public static final String BITVEC = "bitvector operation";
	public static final String BITSHIFT_OVERFLOW = "overflow check for bitwise shift operation";
	public static final String FUNC_POINTER = "call of function pointer";

	@Visualizable
	private final Map<String, ILocation> mReason2Loc;

	public Overapprox(final Map<String, ILocation> reason2Loc) {
		mReason2Loc = reason2Loc;
	}

	public Overapprox(final String reason, final ILocation loc) {
		this(Collections.singletonMap(reason, loc));
	}

	@Visualizable
	private Set<String> getReasonForOverapproximation() {
		return mReason2Loc.keySet();
	}

	public Map<String, ILocation> getOverapproximatedLocations() {
		return mReason2Loc;
	}

	public static Map<String, ILocation> getOverapproximations(final List<? extends IElement> trace) {
		final Map<String, ILocation> result = new HashMap<>();
		for (final IElement elem : trace) {
			final Overapprox overapprox = Overapprox.getAnnotation(elem);
			if (overapprox == null) {
				continue;
			}
			result.putAll(overapprox.getOverapproximatedLocations());
		}
		return result;
	}

	public static <TE extends IElement> Map<String, ILocation>
			getOverapproximations(final IProgramExecution<TE, ?> pe) {
		final Map<String, ILocation> result = new HashMap<>();
		final Iterator<AtomicTraceElement<TE>> iter = pe.iterator();
		while (iter.hasNext()) {
			final TE current = iter.next().getTraceElement();
			final Overapprox overapprox = Overapprox.getAnnotation(current);
			if (overapprox == null) {
				continue;
			}
			result.putAll(overapprox.getOverapproximatedLocations());
		}
		return result;
	}

	@Override
	public String toString() {
		return "Overapprox: " + mReason2Loc;
	}

	public IAnnotations annotate(final IElement elem) {
		return elem.getPayload().getAnnotations().put(Overapprox.class.getName(), this);
	}

	public static Overapprox getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, Overapprox.class.getName(), a -> (Overapprox) a);
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other == this || other == null) {
			return this;
		}
		if (!(other instanceof Overapprox)) {
			return super.merge(other);
		}
		final Overapprox otheroverapprox = (Overapprox) other;
		final Map<String, ILocation> newReasons = new HashMap<>(mReason2Loc);
		for (final Entry<String, ILocation> entry : otheroverapprox.mReason2Loc.entrySet()) {
			final ILocation res = newReasons.putIfAbsent(entry.getKey(), entry.getValue());
			if (res != null) {
				// TODO: This means we "forget" some location
			}
		}
		return new Overapprox(newReasons);
	}
}
