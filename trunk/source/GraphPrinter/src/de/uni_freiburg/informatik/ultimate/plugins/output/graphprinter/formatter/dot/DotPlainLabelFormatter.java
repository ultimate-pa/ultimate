/*
 * Copyright (C) 2026 Manuel Bentele
 *
 * This file is part of the ULTIMATE GraphPrinter plug-in.
 *
 * The ULTIMATE GraphPrinter plug-in is free software: you can redistribute it and/or modify it under the terms of the
 * GNU Lesser General Public License as published by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE GraphPrinter plug-in is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the ULTIMATE GraphPrinter
 * plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE GraphPrinter plug-in, or any
 * covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the ULTIMATE GraphPrinter plug-in grant you
 * additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter.dot;

import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter.LabelFormatter;
import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter.NodeInfo;
import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.preferences.GraphPrinterPreferenceValues.AnnotationMode;

/**
 * {@link LabelFormatter} for {@link AnnotationMode#NONE}.
 *
 * <p>
 * Ignores all metadata and produces plain quoted DOT labels.
 * </p>
 *
 * @author Manuel Bentele
 */
public final class DotPlainLabelFormatter implements LabelFormatter {

	@Override
	public String formatNodeLabel(final String label, final NodeInfo info) {
		return DotFormatter.escapeDotString(label);
	}

	@Override
	public String formatEdgeLabel(final String label, final NodeInfo info) {
		if (label == null || label.isEmpty()) {
			return null;
		}

		return DotFormatter.escapeDotString(label);
	}
}
