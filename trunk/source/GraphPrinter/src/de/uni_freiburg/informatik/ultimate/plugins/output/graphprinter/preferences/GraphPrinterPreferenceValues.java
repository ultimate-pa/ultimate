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

package de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.preferences;

import de.uni_freiburg.informatik.ultimate.core.model.ITool.ModelQuery;

/**
 * Contains labels and default values for the GraphPrinter preference page.
 *
 * @author Manuel Bentele
 */
public class GraphPrinterPreferenceValues {

	/**
	 * Annotation output mode for the graph.
	 */
	public enum AnnotationMode {
		/**
		 * No annotations are included in the formatted graph output.
		 */
		NONE,

		/**
		 * Annotations are included as HTML labels on nodes and edges.
		 */
		HTML_LABELS,

		/**
		 * Annotations are included as separate record nodes connected to their parent.
		 */
		RECORD_NODES
	}

	public static final String LABEL_GRAPH_DIRECTORY = "Graph directory";
	public static final String DEF_GRAPH_DIRECTORY = ".";
	public static final String DESC_GRAPH_DIRECTORY = "Write graph to the specified directory.";

	public static final String LABEL_GRAPH_FILENAME = "Graph filename";
	public static final String DEF_GRAPH_FILENAME = "graph";
	public static final String DESC_GRAPH_FILENAME = "The filename of the generated graph (without file-ending).";

	public static final String LABEL_GRAPH_BESIDES_INPUT_FILE = "Write graph besides input file";
	public static final boolean DEF_GRAPH_BESIDES_INPUT_FILE = true;
	public static final String DESC_GRAPH_BESIDES_INPUT_FILE = "Write graph as \"<inputfilename>_<modeltype>.dot\" "
			+ "in the same directory as the input file. If disabled, the graph is written to the specified graph "
			+ "directory.";

	public static final String LABEL_GRAPH_MODEL = "Graph model to be printed";
	public static final ModelQuery DEF_GRAPH_MODEL = ModelQuery.LAST;
	public static final String DESC_GRAPH_MODEL = "Selects which models are printed by this plugin. "
			+ "ALL prints every model, LAST only the last modified one.";

	public static final String LABEL_GRAPH_ANNOTATION_MODE = "Graph annotation mode";
	public static final AnnotationMode DEF_GRAPH_ANNOTATION_MODE = AnnotationMode.HTML_LABELS;
	public static final String DESC_GRAPH_ANNOTATION_MODE = "Controls how annotations from nodes and edges are "
			+ "included in the graph output. NONE omits annotations, HTML_LABELS embeds them as HTML labels, "
			+ "RECORD_NODES creates separate record nodes connected to each node/edge.";

}
