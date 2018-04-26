/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.core.lib.results;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithLocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;

/**
 * Superclass of all results that are reported for a specific element.
 *
 * @author Matthias Heizmann
 *
 * @param <ELEM>
 *            Type of node of the ultimate model at which this result was obtained.
 */
public abstract class AbstractResultAtElement<ELEM extends IElement> extends AbstractResult
		implements IResultWithLocation {

	private final ELEM mElement;
	protected final IBacktranslationService mTranslatorSequence;

	public AbstractResultAtElement(final ELEM element, final String plugin,
			final IBacktranslationService translatorSequence) {
		super(plugin);
		mElement = element;
		mTranslatorSequence = translatorSequence.getTranslationServiceCopy();
	}

	@Override
	public final ILocation getLocation() {
		return ILocation.getAnnotation(mElement);
	}

	public final ELEM getElement() {
		return mElement;
	}

	public final IBacktranslationService getCurrentBacktranslation() {
		return mTranslatorSequence;
	}

}
