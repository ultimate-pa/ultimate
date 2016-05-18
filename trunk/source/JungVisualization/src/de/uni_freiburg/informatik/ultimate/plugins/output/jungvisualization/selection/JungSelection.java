/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jelena Barth
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2010-2015 pashko
 * 
 * This file is part of the ULTIMATE JungVisualization plug-in.
 * 
 * The ULTIMATE JungVisualization plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE JungVisualization plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE JungVisualization plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE JungVisualization plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE JungVisualization plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.selection;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IElementSelection;

/**
 * Provides access to nodes.
 * @see {@link IElementSelection}
 * @author lena
 *
 */
public class JungSelection implements IElementSelection {
	
	private IElement mSelectedNodePayload;
	
	
	public JungSelection() {
		mSelectedNodePayload = null;
	}

	@Override
	public IElement getElement() {
		return mSelectedNodePayload;
		
	}

	@Override
	public boolean isEmpty() {
		return (mSelectedNodePayload == null);
	}

	@Override
	public void setElement(IElement payload) {
		mSelectedNodePayload = payload;
	}

}
