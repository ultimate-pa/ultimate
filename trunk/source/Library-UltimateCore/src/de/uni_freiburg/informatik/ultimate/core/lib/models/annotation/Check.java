/*
 * Copyright (C) 2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
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

import java.util.EnumSet;
import java.util.Iterator;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IMessageProvider;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;

/**
 * Specification that should be checked at position
 *
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @author Matthias Heizmann
 */
public class Check extends ModernAnnotations {

	private static final String MSG_AND = " and ";

	private static final long serialVersionUID = -3753413284642976683L;

	private static final String KEY = Check.class.getName();

	@Visualizable
	private final Set<Spec> mSpec;

	private final IMessageProvider mMsgProvider;

	public Check(final Spec spec) {
		this(EnumSet.of(spec));
	}

	public Check(final Spec spec, final IMessageProvider msgProvider) {
		this(EnumSet.of(spec), msgProvider);
	}

	public Check(final Set<Spec> newSpec) {
		this(newSpec, new CheckMessageProvider());
	}

	public Check(final Set<Spec> newSpec, final IMessageProvider msgProvider) {
		assert !newSpec.isEmpty();
		mSpec = newSpec;
		mMsgProvider = msgProvider;
	}

	public Set<Spec> getSpec() {
		return mSpec;
	}

	protected IMessageProvider getMessageProvider() {
		return mMsgProvider;
	}

	public String getPositiveMessage() {
		return getCompoundMessage(mMsgProvider::getPositiveMessage);
	}

	public String getNegativeMessage() {
		return getCompoundMessage(mMsgProvider::getNegativeMessage);
	}

	private String getCompoundMessage(final Function<Spec, String> msgProviderFunc) {
		final Iterator<Spec> iter = mSpec.iterator();
		if (mSpec.size() == 1) {
			return msgProviderFunc.apply(iter.next());
		}

		final StringBuilder sb = new StringBuilder();
		while (iter.hasNext()) {
			sb.append(msgProviderFunc.apply(iter.next())).append(MSG_AND);
		}
		sb.delete(sb.length() - MSG_AND.length(), sb.length());
		return sb.toString();
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other == null) {
			return this;
		}
		if (other == this) {
			return this;
		}
		if (!(other instanceof Check)) {
			throw new UnmergeableAnnotationsException(this, other);
		}
		final Check otherCheck = (Check) other;

		final EnumSet<Spec> newSpec = EnumSet.copyOf(mSpec);
		newSpec.addAll(otherCheck.getSpec());
		// note: automatic merging looses all information about message providers and uses the default ones
		return new Check(newSpec);
	}

	/**
	 * Adds this Check object to the annotations of a IElement.
	 *
	 * @param node
	 *            the element
	 */
	public void annotate(final IElement node) {
		node.getPayload().getAnnotations().put(KEY, this);
	}

	/**
	 * Return the checked specification that is checked at this location or null.
	 */
	public static Check getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, KEY, a -> (Check) a);
	}

	public static Check mergeCheck(final Check one, final Check other) {
		if (one == null) {
			return other;
		}
		if (other == null) {
			return one;
		}
		return (Check) one.merge(other);
	}

	@Override
	public String toString() {
		return mSpec.stream().map(Spec::toString).collect(Collectors.joining(MSG_AND));
	}

	@Override
	public int hashCode() {
		return toString().hashCode();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final Check other = (Check) obj;
		if (mSpec == null) {
			if (other.mSpec != null) {
				return false;
			}
		} else if (!mSpec.equals(other.mSpec)) {
			return false;
		}
		return true;
	}

}
