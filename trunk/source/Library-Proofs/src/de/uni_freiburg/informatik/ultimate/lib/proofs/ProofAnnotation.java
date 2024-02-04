/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;

/**
 * Annotates a program (such as an ICFG) with one or more proofs.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class ProofAnnotation extends ModernAnnotations {
	private static final long serialVersionUID = -9142656546325935187L;

	private static final String KEY = ProofAnnotation.class.getName();

	@Visualizable
	private final List<Object> mProofs;

	private ProofAnnotation(final List<Object> proofs) {
		mProofs = proofs;
	}

	public List<Object> getProofs() {
		return Collections.unmodifiableList(mProofs);
	}

	public static void addProof(final IElement element, final Object proof) {
		final IAnnotations annot = element.getPayload().getAnnotations().get(KEY);

		final var proofs = new ArrayList<>();
		if (annot != null) {
			proofs.addAll(((ProofAnnotation) annot).getProofs());
		}
		proofs.add(proof);

		final var newAnnot = new ProofAnnotation(proofs);
		element.getPayload().getAnnotations().put(KEY, newAnnot);
	}

	public static List<Object> getProofs(final IElement element) {
		final IAnnotations annot = element.getPayload().getAnnotations().get(KEY);
		if (annot == null) {
			return Collections.emptyList();
		}
		return ((ProofAnnotation) annot).getProofs();
	}

	public static <T> List<T> getProofs(final IElement element, final Class<T> typeOfProof) {
		final IAnnotations annot = element.getPayload().getAnnotations().get(KEY);
		if (annot == null) {
			return Collections.emptyList();
		}
		return ((ProofAnnotation) annot).getProofs().stream().filter(typeOfProof::isInstance).map(typeOfProof::cast)
				.collect(Collectors.toList());
	}
}
