/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermWrapper;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Wrapper for named terms. Allows us to access name and subterm directly. Named
 * terms are defined in 3.6.6 of the SMT-LIB 2.6 standard
 * http://smtlib.cs.uiowa.edu/language.shtml This class has a shortcoming, it
 * does not work for terms with several attributes. We however presume that such
 * terms will not occur in our applications.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class NamedTermWrapper implements ITermWrapper {

	final Term mOriginalTerm;
	final Term mSubTerm;
	final String mName;

	public NamedTermWrapper(final Term originalTerm, final Term subTerm, final String name) {
		super();
		mOriginalTerm = originalTerm;
		mSubTerm = subTerm;
		mName = name;
	}

	@Override
	public Term getTerm() {
		return mOriginalTerm;
	}

	public Term getSubTerm() {
		return mSubTerm;
	}

	public String getName() {
		return mName;
	}

	public static NamedTermWrapper of(final Term term) {
		if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm annotTerm = (AnnotatedTerm) term;
			final Annotation[] annot = annotTerm.getAnnotations();
			if (annot.length == 1) {
				if (annot[0].getKey().equals(":named")) {
					final Object value = annot[0].getValue();
					if (value instanceof String) {
						final String name = (String) value;
						return new NamedTermWrapper(term, annotTerm.getSubterm(), name);
					}
				}
			}
		}
		return null;
	}



}
