/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class UltimatePreferenceItemGroup extends BaseUltimatePreferenceItem {
	private final String mLabel;
	private final String mDescription;
	private final List<BaseUltimatePreferenceItem> mItems;

	public UltimatePreferenceItemGroup(final String label, final BaseUltimatePreferenceItem... items) {
		this(label, null, items);
	}

	public UltimatePreferenceItemGroup(final String label, final String description,
			final BaseUltimatePreferenceItem... items) {
		this(label, description, Arrays.asList(items));
	}

	public UltimatePreferenceItemGroup(final String label, final String description,
			final List<BaseUltimatePreferenceItem> items) {
		mLabel = label;
		mDescription = description;
		mItems = items;
	}

	public String getLabel() {
		return mLabel;
	}

	public String getDescription() {
		return mDescription;
	}

	public List<BaseUltimatePreferenceItem> getItems() {
		return mItems;
	}

	@Override
	public PreferenceType getType() {
		return PreferenceType.Group;
	}

	@Override
	public List<UltimatePreferenceItem<?>> getFlattenedList() {
		return mItems.stream().flatMap(item -> item.getFlattenedList().stream()).collect(Collectors.toList());
	}
}
