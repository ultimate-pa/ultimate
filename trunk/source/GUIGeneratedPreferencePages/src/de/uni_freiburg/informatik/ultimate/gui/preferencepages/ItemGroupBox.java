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
package de.uni_freiburg.informatik.ultimate.gui.preferencepages;

import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;

/**
 * Used by {@link UltimateGeneratedPreferencePage} to group related preference items.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
class ItemGroupBox {
	private static final int MARGIN = 20;

	private final Group mGroup;
	private final Label mDescription;
	private final Composite mItemContainer;

	public ItemGroupBox(final String label, final String description, final Composite parent, final int numColumns) {
		mGroup = createGroup(label, parent, numColumns);
		mDescription = createDescription(parent, mGroup, description, numColumns);
		mItemContainer = createItemContainer(parent, mGroup, numColumns);
	}

	Composite getFieldEditorParent() {
		return mItemContainer;
	}

	void adjustForNumColumns(final int numColumns) {
		((GridData) mGroup.getLayoutData()).horizontalSpan = numColumns;
		((GridLayout) mItemContainer.getLayout()).numColumns = numColumns;
	}

	private static Group createGroup(final String label, final Composite parent, final int numColumns) {
		final var group = new Group(parent, SWT.SHADOW_IN);

		// position group in the parent
		final var gd = new GridData(SWT.FILL, GridData.CENTER, true, false, numColumns, 1);
		gd.verticalIndent = MARGIN;
		group.setLayoutData(gd);

		// make font bold
		final var fontData = parent.getFont().getFontData();
		for (final var fd : fontData) {
			fd.setStyle(SWT.BOLD);
		}
		final var font = new Font(parent.getFont().getDevice(), fontData);
		group.setFont(font);

		// set group label
		group.setText(label);

		// layout for group content
		group.setLayout(new GridLayout(1, true));

		return group;
	}

	private static Composite createItemContainer(final Composite root, final Group group, final int numColumns) {
		final var container = new Composite(group, 0);
		container.setFont(root.getFont());

		final var gd = new GridData(SWT.FILL, SWT.CENTER, true, false, 1, 1);
		gd.horizontalIndent = MARGIN;
		container.setLayoutData(gd);

		container.setLayout(new GridLayout(numColumns, false));
		return container;
	}

	private static Label createDescription(final Composite root, final Group parent, final String description,
			final int numColumns) {
		if (description == null) {
			return null;
		}
		final var label = new Label(parent, SWT.LEFT | SWT.WRAP);
		label.setFont(root.getFont());
		label.setText(description);
		label.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false, numColumns, 1));
		return label;
	}
}