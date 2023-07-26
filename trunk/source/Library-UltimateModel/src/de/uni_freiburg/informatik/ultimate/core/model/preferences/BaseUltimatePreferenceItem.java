/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
 * Interface for any Ultimate preference item.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class BaseUltimatePreferenceItem {

	/**
	 * @return The type of the Ultimate Preference Item.
	 */
	public abstract PreferenceType getType();

	/**
	 * @return A list that contains the current preference item. If the item is a container item, the flattened list of
	 *         all container elements is constructed.
	 */
	public abstract List<UltimatePreferenceItem<?>> getFlattenedList();

	/**
	 * Constructs a flattened list out of a given list of {@link BaseUltimatePreferenceItem}s.
	 * 
	 * @param list
	 *            The input list.
	 * @return A flattened list.
	 */
	public static List<UltimatePreferenceItem<?>> constructFlattenedList(final List<BaseUltimatePreferenceItem> list) {
		final List<UltimatePreferenceItem<?>> returnList = new ArrayList<>();

		for (final BaseUltimatePreferenceItem elem : list) {
			returnList.addAll(elem.getFlattenedList());
		}

		return returnList;
	}

	/**
	 * Constructs a flattened list out of a given list of {@link BaseUltimatePreferenceItem}s.
	 * 
	 * @param list
	 *            The input list.
	 * @return A flattened list.
	 */
	public static List<UltimatePreferenceItem<?>> constructFlattenedList(final BaseUltimatePreferenceItem[] list) {
		final List<UltimatePreferenceItem<?>> returnList = new ArrayList<>();

		for (int i = 0; i < list.length; i++) {
			returnList.addAll(list[i].getFlattenedList());
		}

		return returnList;
	}

	/**
	 * Constructs a flattened array out of a given list of {@link BaseUltimatePreferenceItem}s.
	 * 
	 * @param list
	 *            The input list.
	 * @return A flattened list.
	 */
	public static UltimatePreferenceItem<?>[] constructFlattenedArray(final BaseUltimatePreferenceItem[] list) {
		final List<UltimatePreferenceItem<?>> returnList = constructFlattenedList(list);

		return returnList.toArray(new UltimatePreferenceItem<?>[returnList.size()]);
	}
}