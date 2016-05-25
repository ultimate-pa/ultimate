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

import de.uni_freiburg.informatik.ultimate.core.model.IController;

/**
 * Interface for any Ultimate preference item.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class BaseUltimatePreferenceItem {

	boolean mUseCustomPreferencePage;

	/**
	 * PreferenceType describes how a preference item should be presented to the user by the active {@link IController}.
	 * 
	 * @author dietsch
	 * 
	 */
	public enum PreferenceType {
		/**
		 * Yes/no choice. Usually a single check-box or a flag.
		 */
		Boolean,
		/**
		 * A string representing an absolute path to a single directory on the local file system.
		 */
		Directory,
		/**
		 * A single line of text.
		 */
		String,
		/**
		 * A non-editable label that can be used to describe parts of the preferences.
		 * 
		 * @see {@link UltimatePreferenceInitializer#initializeDefaultPreferences()} for more information on positioning
		 *      {@link UltimatePreferenceItem UltimatePreferenceItems}.
		 */
		Label,
		/**
		 * Presents the user with a single choice from some predefined values. Can be used for e.g. Enums.
		 * 
		 * Differs from {@link #Radio} because the guideline is that Combo does not show all values simultaneously
		 * (think Combobox, Radiobuttons/Radiolist).
		 */
		Combo,
		/**
		 * Presents the user with a single choice from some predefined values. Can be used for e.g. Enums.
		 * 
		 * Differs from {@link #Combo} because the guideline is that Radio shows all values simultaneously.
		 */
		Radio,
		/**
		 * A single number representing an Integer.
		 */
		Integer,
		/**
		 * A string representing one or multiple paths to a file or directory on the system. If multiple paths are
		 * specified by the user, they are separated by a semicolon.
		 */
		Path,
		/**
		 * A string spanning multiple lines. The lines are separated by the system-default line break character (e.g. \r
		 * or \n).
		 */
		MultilineString,
		/**
		 * A string representing an absolute path on the local file system to a single file.
		 */
		File,
		/**
		 * A string representing a color. The string has to be of the form "red,green,blue", where 0 <= red,green,blue
		 * <= 255.
		 */
		Color,
		/**
		 * A container of sub preference items.
		 */
		SubItemContainer,
	}

	/**
	 * @return The type of the Ultimate Preference Item.
	 */
	public abstract PreferenceType getType();

	/**
	 * @return A list that contains the current preference item. If the item is a container item, the flattened list of
	 *         all container elements is constructed.
	 */
	public abstract List<UltimatePreferenceItem<?>> getFlattenedList();

	public boolean getUseCustomPreferencePage() {
		return mUseCustomPreferencePage;
	}

	/**
	 * Constructs a flattened list out of a given list of {@link BaseUltimatePreferenceItem}s.
	 * 
	 * @param list
	 *            The input list.
	 * @return A flattened list.
	 */
	public static List<UltimatePreferenceItem<?>> constructFlattenedList(List<BaseUltimatePreferenceItem> list) {
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
	public static List<UltimatePreferenceItem<?>> constructFlattenedList(BaseUltimatePreferenceItem[] list) {
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
	public static UltimatePreferenceItem<?>[] constructFlattenedArray(BaseUltimatePreferenceItem[] list) {
		final List<UltimatePreferenceItem<?>> returnList = constructFlattenedList(list);

		return returnList.toArray(new UltimatePreferenceItem<?>[returnList.size()]);
	}
}