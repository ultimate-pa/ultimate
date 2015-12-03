/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.core.services.model.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Report that some syntax is not (yet?) supported by our implementation 
 * (e.g. input is program that uses arrays but solver setting uses logic that
 * does not support arrays) .
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class UnsupportedSyntaxResult<ELEM extends IElement> 
						extends AbstractResult implements IResultWithLocation {
	
	private final ELEM m_Position;
	protected final IBacktranslationService m_TranslatorSequence;
	private final ILocation m_Location;
	private String m_LongDescription;

	/**
	 * @param location
	 * @param syntaxErrorType
	 */
	public UnsupportedSyntaxResult(ELEM position, String plugin, 
			IBacktranslationService translatorSequence, String longDescription) {
		super(plugin);
		m_Position = position;
		m_TranslatorSequence = translatorSequence;
		m_Location = null;
		m_LongDescription = longDescription;
	}
	
	public UnsupportedSyntaxResult(String plugin, ILocation location,
			String longDescription) {
		super(plugin);
		m_Position = null;
		m_TranslatorSequence = null;
		m_Location = location;
		m_LongDescription = longDescription;
	}

	@Override
	public String getShortDescription() {
		return "Unsupported Syntax";
	}

	@Override
	public String getLongDescription() {
		return m_LongDescription;
	}
	
	public final ILocation getLocation() {
		assert ((m_Position == null) ^ (m_Location == null)) : 
			"exactly one has to be non-null";
		if (m_Position != null) {
			return m_Position.getPayload().getLocation();
		} else {
			return m_Location;
		}
	}

	public final ELEM getElement() {
		return m_Position;
	}

	
}
