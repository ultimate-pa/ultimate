/*
 * Copyright (C) 2013-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BlockEncoding plug-in.
 * 
 * The ULTIMATE BlockEncoding plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BlockEncoding plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncoding plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncoding plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BlockEncoding plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating.util;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;


/**
 * To create an rating heuristic, which can decide on basis of the underlying
 * program, we need to store some statistical properties, which we can use for
 * that. <br>
 * So for example, the amount of edges in the graph, or the amount of
 * disjunctions used in the minimization, or the amount of variables, and so
 * on...
 * 
 * @author Stefan Wissert
 * 
 */
public class EncodingStatistics {

	/**
	 * stores the total amount of basic edges in the original graph
	 */
	public static int countOfBasicEdges;

	/**
	 * stores the total amount of created disjunctions (minimizing parallel
	 * edges), this is useful because it seems to be good, to break at some
	 * amount of disjunctions
	 */
	public static int countOfDisjunctions;

	/**
	 * stores the maximum number of disjunctions, which are contained in one
	 * composite edge
	 */
	public static int maxDisjunctionsInOneEdge;
	
	/**
	 * stores the maximum number of elements in one single disjunction
	 */
	public static int maxElementsInOneDisjunction;
	
	/**
	 * stores the max. number of variables used in one edge
	 */
	public static int maxDiffVariablesInOneEdge;
	
	/**
	 * stores the min. number of variables used in one edge
	 */
	public static int minDiffVariablesInOneEdge;
	
	/**
	 * stores the computed rating value of the total converted graph.
	 */
	public static int totalRCFGRating;
	
	/**
	 * counts the remaining edges in the RCFG.
	 */
	public static int edgesInRCFG;
	
	/**
	 * stores the max. rating value computed for one edge
	 */
	public static int maxRatingInOneEdge;
	
	public static IMinimizedEdge maxRatedEdge;
	
	/**
	 * Initializes, all stored statistics. This have to be done, before we start
	 * a new run of block encoding.
	 */
	public static void init() {
		countOfBasicEdges = 0;
		countOfDisjunctions = 0;
		maxDisjunctionsInOneEdge = 0;
		maxElementsInOneDisjunction = 0;
		maxDiffVariablesInOneEdge = 0;
		minDiffVariablesInOneEdge = Integer.MAX_VALUE;
		totalRCFGRating = 0;
		edgesInRCFG = 0;
		maxRatedEdge = null;
		maxRatingInOneEdge = 0;
	}

	/**
	 * 
	 */
	public static void incCountOfBasicEdges() {
		countOfBasicEdges++;
	}

	/**
	 * 
	 */
	public static void incCountOfDisjunctions() {
		countOfDisjunctions++;
	}
	
	/**
	 * @param value
	 */
	public static void setMaxDisjunctionsInOneEdge(int value) {
		if (value > maxDisjunctionsInOneEdge) {
			maxDisjunctionsInOneEdge = value;
		}
	}
	
	/**
	 * @param value
	 */
	public static void setMaxElementsInOneDisjunction(int value) {
		if (value > maxElementsInOneDisjunction) {
			maxElementsInOneDisjunction = value;
		}
	}
	
	/**
	 * @param value
	 */
	public static void setMaxMinDiffVariablesInOneEdge(int value) {
		// we ignore zero
		if (value == 0) {
			return;
		}
		if (value > maxDiffVariablesInOneEdge) {
			maxDiffVariablesInOneEdge = value;
		}
		if (value < minDiffVariablesInOneEdge) {
			minDiffVariablesInOneEdge = value;
		}
	}
	
	/**
	 * @param ratingValue
	 */
	public static void addToTotalRating(int ratingValue) {
		totalRCFGRating = totalRCFGRating + ratingValue;
	}
	
	/**
	 * 
	 */
	public static void incTotalEdges() {
		edgesInRCFG++;
	}
	
	public static void setMaxRatingOneEdge(int val, IMinimizedEdge edge) {
		if (val > maxRatingInOneEdge) {
			maxRatedEdge = edge;
			maxRatingInOneEdge = val;
		}
	}
	
	public static String reportStatistics() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Total Rating Value: " + totalRCFGRating + "\n");
		sb.append("Number of Edges in the RCFG: " + edgesInRCFG + "\n");
		return sb.toString();
	}
}
