/*
 * Copyright (C) 2014-2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE GUIGeneratedPreferencePages plug-in.
 * 
 * The ULTIMATE GUIGeneratedPreferencePages plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE GUIGeneratedPreferencePages plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE GUIGeneratedPreferencePages plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE GUIGeneratedPreferencePages plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE GUIGeneratedPreferencePages plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.core.model.preferences;

import java.util.ArrayList;
import java.util.List;

/**
 * Ultimate Preference container item.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public final class UltimatePreferenceItemContainer extends BaseUltimatePreferenceItem {

	private final List<BaseUltimatePreferenceItem> mContainerItems;
	private final String mContainerName;

	public UltimatePreferenceItemContainer(final String containerName) {
		mContainerItems = new ArrayList<>();
		mContainerName = containerName;
	}

	@Override
	public PreferenceType getType() {
		return PreferenceType.SubItemContainer;
	}

	public void addItem(final BaseUltimatePreferenceItem item) {
		mContainerItems.add(item);
	}

	public void addAbstractItems(final List<BaseUltimatePreferenceItem> items) {
		mContainerItems.addAll(items);
	}
	
	public void addItems(final List<UltimatePreferenceItem<?>> items) {
		mContainerItems.addAll(items);
	}

	public List<BaseUltimatePreferenceItem> getContainerItems() {
		return mContainerItems;
	}
	
	@Override
	public List<UltimatePreferenceItem<?>> getFlattenedList() {
		final List<UltimatePreferenceItem<?>> returnList = new ArrayList<>();
		
		for (final BaseUltimatePreferenceItem item : mContainerItems) {
			returnList.addAll(item.getFlattenedList());
		}
		
		return returnList;
	}
	
	public String getContainerName() {
		return mContainerName;
	}
}
